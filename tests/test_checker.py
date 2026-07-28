"""Tests for the SafeVerify checker's exec orchestration and the scorer wiring.

``SandboxSafeVerify`` runs in two phases across two sandboxes. In the UNTRUSTED
``compile`` sandbox (5 execs): clear scratch, unpack the submission tar into
``Submission/``, check the entry module is present, and compile it standalone
(``-o submission.olean``) -- this elaborates agent Lean, so it is isolated here.
It then reads the olean bytes out. In the TRUSTED ``scorer`` sandbox (4 execs):
clear scratch, compile the trusted target at ``Submission/Spec.lean`` (``-o
target.olean``), write the submission olean in, and run ``safe_verify`` on the
two oleans -- no agent Lean is elaborated here. A fake sandbox (serving both
names) scripts the flat global exec order to verify the verdict mapping; the real
``safe_verify`` exe is validated against the toolchain. The scorer tests use a
stub checker and a fake workspace sandbox to verify the ``Submission/`` tar is
collected and handed to the checker as raw bytes.
"""

from __future__ import annotations

from collections.abc import Sequence
from pathlib import Path
from types import SimpleNamespace

import pytest
from inspect_ai.model import ModelName
from inspect_ai.scorer import CORRECT, INCORRECT, Score, Target
from inspect_ai.solver import TaskState
from inspect_ai.util import ExecResult, OutputLimitExceededError

import apn.checker as checker_mod
import apn.scorer as scorer_mod
from apn.checker import CheckOutcome, SafeVerifyChecker, SandboxSafeVerify
from apn.layout import ENTRY_PATH, ENTRY_REL, SUBMISSION_DIR
from apn.scorer import proof_scorer

SKETCH = "import Mathlib\ntheorem tgt : True := by sorry\n"
# The submission is now opaque tar bytes; the checker unpacks them in its own
# sandbox. The scripted orchestration tests don't parse them.
SUBMISSION_TAR = b"fake-submission-tar-bytes"


class StubChecker:
    def __init__(
        self, ok: bool, report: list[dict[str, object]] | None = None
    ) -> None:
        self._ok = ok
        self._report = report
        self.calls: list[bytes] = []

    async def check(self, target: str, submission_tar: bytes) -> CheckOutcome:
        self.calls.append(submission_tar)
        return CheckOutcome(
            ok=self._ok, stage="stub", detail="stub outcome", report=self._report
        )


class FakeSandbox:
    """Stands in for the agent's workspace sandbox: serves a fixed Submission tar.

    ``read_submission_tar`` runs ``tar``/``rm`` execs and reads the tar back, so
    this records execs and returns the scripted tar bytes from ``read_file``.
    """

    def __init__(self, tar: bytes) -> None:
        self._tar = tar
        self.execs: list[list[str]] = []

    async def exec(self, cmd: list[str], **kwargs: object) -> ExecResult[str]:
        self.execs.append(cmd)
        return ExecResult(success=True, returncode=0, stdout="", stderr="")

    async def read_file(self, file: str, text: bool = True) -> bytes:
        return self._tar


# --------------------------------------------------------------------------- #
# SandboxSafeVerify exec orchestration                                         #
# --------------------------------------------------------------------------- #


# A scripted step is either an ExecResult the fake exec returns, or an
# exception the fake exec raises -- the sandbox provider *raises* (rather than
# returns) on a timeout (TimeoutError) and on an undecodable output byte
# (UnicodeDecodeError), so the checker has to catch those at the .exec() call.
Step = ExecResult[str] | BaseException


_OLEAN_BYTES = b"compiled-submission-olean-bytes"


class ScriptedSandbox:
    """A stub serving BOTH the compile and scorer sandboxes (the monkeypatched
    ``sandbox(name)`` returns this same object for either name). It records the
    flat global sequence of writes/execs/reads and returns/raises scripted steps.

    ``read_file`` dispatches on the path: the compile-sandbox olean read returns
    ``olean`` bytes (or raises ``FileNotFoundError`` when ``olean is None`` -- a
    clean compile that left no readable olean, or raises ``olean`` itself when it
    is an exception -- e.g. an ``OutputLimitExceededError`` for an oversized
    olean), and the scorer-sandbox report read returns ``report`` (a string),
    raises ``FileNotFoundError`` when it is ``None`` (safe_verify wrote nothing),
    or raises ``report`` itself when it is an exception (e.g. an
    ``OutputLimitExceededError`` for an oversized report).
    """

    def __init__(
        self,
        results: Sequence[Step],
        report: str | BaseException | None = None,
        olean: bytes | BaseException | None = _OLEAN_BYTES,
    ) -> None:
        self._results = list(results)
        self._report = report
        self._olean = olean
        self.written: dict[str, object] = {}
        self.writes: list[tuple[str, object]] = []
        self.commands: list[list[str]] = []
        self.reads: list[str] = []

    async def write_file(self, file: str, contents: object) -> None:
        self.written[file] = contents
        self.writes.append((file, contents))

    async def exec(self, cmd: list[str], **kwargs: object) -> ExecResult[str]:
        self.commands.append(cmd)
        step = self._results.pop(0)
        if isinstance(step, BaseException):
            raise step
        return step

    async def read_file(self, file: str, text: bool = True) -> str | bytes:
        self.reads.append(file)
        if file == checker_mod.COMPILE_SUBMISSION_OLEAN:
            if self._olean is None:
                raise FileNotFoundError(file)
            if isinstance(self._olean, BaseException):
                raise self._olean
            return self._olean
        if self._report is None:
            raise FileNotFoundError(file)
        if isinstance(self._report, BaseException):
            raise self._report
        return self._report


def _ok(stderr: str = "") -> ExecResult[str]:
    return ExecResult(success=True, returncode=0, stdout="", stderr=stderr)


def _fail(returncode: int, stderr: str = "") -> ExecResult[str]:
    return ExecResult(success=False, returncode=returncode, stdout="", stderr=stderr)


def _timeout() -> TimeoutError:
    # Matches the k8s sandbox provider's message; it raises a builtin
    # TimeoutError on exit code 124 (k8s_sandbox/_pod/execute.py).
    return TimeoutError("Command timed out after 900s. ExecResult(returncode=124)")


def _decode_error() -> UnicodeDecodeError:
    # The provider decodes command output before returning it; a non-utf8 byte
    # raises UnicodeDecodeError out of .exec() (it never reaches our code).
    return UnicodeDecodeError("utf-8", b"\xff", 0, 1, "invalid start byte")


def _oversize_error() -> OutputLimitExceededError:
    # The provider raises this out of read_file when the artifact exceeds
    # MAX_READ_FILE_SIZE (k8s_sandbox/_pod/read.py); the 100 MiB default matches
    # what the production logs showed.
    return OutputLimitExceededError(limit_str="100 MiB", truncated_output=None)


def _checker(
    monkeypatch: pytest.MonkeyPatch,
    results: Sequence[Step],
    allow_disproofs: bool = True,
    report: str | BaseException | None = None,
    olean: bytes | BaseException | None = _OLEAN_BYTES,
) -> tuple[SandboxSafeVerify, ScriptedSandbox]:
    sb = ScriptedSandbox(results, report=report, olean=olean)
    monkeypatch.setattr(checker_mod, "sandbox", lambda *a, **k: sb)
    return SandboxSafeVerify(allow_disproofs=allow_disproofs), sb


# The nine execs of the happy path, in global order. COMPILE sandbox (5): clear,
# mkdir, unpack submission, check entry present, compile submission. Then the
# olean is read out. SCORER sandbox (4): clear, mkdir, compile trusted target,
# run safe_verify.
def _accept_steps() -> list[Step]:
    steps: list[Step] = [_ok()] * 8
    steps.append(_ok("SafeVerify check passed."))
    return steps


async def test_check_accepts_when_all_steps_pass(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, sb = _checker(monkeypatch, _accept_steps())
    outcome = await checker.check("the target", SUBMISSION_TAR)
    assert outcome.ok
    assert outcome.stage == "safeverify"
    # Three writes (submission tar, then target spec, then the submission olean
    # copied into the scorer); nine commands (5 compile-sandbox + 4 scorer).
    assert len(sb.writes) == 3
    assert len(sb.commands) == 9
    assert sb.commands[0][:2] == ["rm", "-rf"]
    assert sb.commands[1][:2] == ["mkdir", "-p"]


async def test_check_compiles_in_two_phases_across_sandboxes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Phase 1 (UNTRUSTED compile sandbox): unpack + compile the submission to an
    # olean. Phase 2 (TRUSTED scorer sandbox): compile the trusted target at the
    # same entry path (so Lean gives each module name Submission.Spec -- load-
    # bearing for private-name matching) and run safe_verify on the two oleans.
    checker, sb = _checker(monkeypatch, _accept_steps())
    await checker.check("THE TARGET", b"THE TAR")

    # --- compile phase --------------------------------------------------------
    # Submission tar staged in the compile sandbox, unpacked into SUBMISSION_DIR.
    assert sb.writes[0] == (checker_mod.COMPILE_SUBMISSION_TAR, b"THE TAR")
    assert sb.commands[0][:2] == ["rm", "-rf"]
    assert sb.commands[1][:2] == ["mkdir", "-p"]
    assert sb.commands[2] == [
        "tar", "-xf", checker_mod.COMPILE_SUBMISSION_TAR, "-C", SUBMISSION_DIR
    ]
    assert sb.commands[3] == ["test", "-f", ENTRY_PATH]
    # Submission compiled standalone to the compile-sandbox olean.
    assert sb.commands[4] == [
        "lake", "env", "lean", "-o",
        checker_mod.COMPILE_SUBMISSION_OLEAN, ENTRY_REL,
    ]
    # The produced olean is read out of the compile sandbox.
    assert checker_mod.COMPILE_SUBMISSION_OLEAN in sb.reads

    # --- verify phase ---------------------------------------------------------
    # Trusted target written + compiled standalone at the SAME entry path.
    assert sb.writes[1] == (ENTRY_PATH, "THE TARGET")
    assert sb.commands[5][:2] == ["rm", "-rf"]
    assert sb.commands[6][:2] == ["mkdir", "-p"]
    assert sb.commands[7] == [
        "lake", "env", "lean", "-o", checker_mod.TARGET_OLEAN, ENTRY_REL
    ]
    # The olean read out of the compile sandbox is written into the scorer.
    assert sb.writes[2] == (checker_mod.SUBMISSION_OLEAN, _OLEAN_BYTES)
    # safe_verify runs on the two oleans, target then submission.
    assert sb.commands[8][-2:] == [checker_mod.TARGET_OLEAN, checker_mod.SUBMISSION_OLEAN]


async def test_check_rejects_when_untar_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A malformed/forged submission archive: clear, mkdir, then `tar -xf` fails
    # in the compile sandbox -> a verdict on the agent's code, not a raise.
    checker, sb = _checker(monkeypatch, [_ok(), _ok(), _fail(2, "tar: bad")])
    outcome = await checker.check("the target", SUBMISSION_TAR)
    assert not outcome.ok
    assert outcome.stage == "compile_submission"
    # Nothing ran past the failed untar (no compile, no olean read, no verify).
    assert len(sb.commands) == 3
    assert sb.reads == []


async def test_check_rejects_when_entry_module_missing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A submission whose tar omits Spec.lean: the post-unpack `test -f` (4th
    # command) fails -> rejected as a verdict, NOT raised. Nothing is compiled.
    checker, sb = _checker(monkeypatch, [_ok(), _ok(), _ok(), _fail(1)])
    outcome = await checker.check("the target", SUBMISSION_TAR)
    assert not outcome.ok
    assert outcome.stage == "compile_submission"
    assert "entry module missing" in outcome.detail
    assert len(sb.commands) == 4
    assert sb.reads == []


async def test_check_rejects_when_compiled_olean_missing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A clean compile (5 ok execs) that leaves no readable olean -- e.g. a
    # backgrounded process the #eval spawned deleted it -> a verdict on the
    # agent's code, never reaching the scorer.
    checker, sb = _checker(monkeypatch, [_ok()] * 5, olean=None)
    outcome = await checker.check("the target", SUBMISSION_TAR)
    assert not outcome.ok
    assert outcome.stage == "compile_submission"
    assert "no readable olean" in outcome.detail
    # The compile sandbox ran its 5 execs; the scorer phase never started.
    assert len(sb.commands) == 5


async def test_check_rejects_when_compiled_olean_too_large(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A clean compile (5 ok execs) whose olean is too large to read back out of
    # the sandbox (OutputLimitExceededError, the MAX_READ_FILE_SIZE limit). That
    # is the agent's expensive proof term inflating the artifact -- deterministic
    # per submission, so rerunning could never help. A verdict on the agent's
    # code, never reaching the scorer, not a raise that errors the sample.
    checker, sb = _checker(monkeypatch, [_ok()] * 5, olean=_oversize_error())
    outcome = await checker.check("the target", SUBMISSION_TAR)
    assert not outcome.ok
    assert outcome.stage == "compile_submission_oversize"
    # The compile sandbox ran its 5 execs; the scorer phase never started.
    assert len(sb.commands) == 5


async def test_check_passes_disproofs_flag_to_safe_verify(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # By default the agent may disprove a conjecture, so safe_verify is invoked
    # with --disproofs (it then accepts foo OR foo.disproof for each target).
    checker, sb = _checker(monkeypatch, _accept_steps())
    outcome = await checker.check("the target", SUBMISSION_TAR)
    assert outcome.ok
    safe_verify_cmd = sb.commands[8]
    assert "--disproofs" in safe_verify_cmd
    # --save requests the JSON report; the two olean paths stay positional last.
    assert "--save" in safe_verify_cmd
    assert safe_verify_cmd[-2].endswith("target.olean")
    assert safe_verify_cmd[-1].endswith("submission.olean")


async def test_check_omits_disproofs_flag_when_disabled(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, sb = _checker(monkeypatch, _accept_steps(), allow_disproofs=False)
    await checker.check("the target", SUBMISSION_TAR)
    assert "--disproofs" not in sb.commands[8]


async def test_check_attaches_safeverify_report(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # safe_verify's --save JSON is read back and attached to the outcome.
    report = '[{"targetInfo": {"constInfo": {"kind": "theorem"}}, "failureMode": null}]'
    checker, sb = _checker(monkeypatch, _accept_steps(), report=report)
    outcome = await checker.check("the target", SUBMISSION_TAR)
    assert outcome.ok
    assert outcome.report == [
        {"targetInfo": {"constInfo": {"kind": "theorem"}}, "failureMode": None}
    ]
    # Two reads: the compile-sandbox olean, then the scorer-sandbox report.
    assert sb.reads == [checker_mod.COMPILE_SUBMISSION_OLEAN, checker_mod.REPORT_PATH]


async def test_check_report_is_none_when_safe_verify_wrote_nothing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A resource death can leave no report file; a missing read is not an error.
    checker, _ = _checker(monkeypatch, [_ok()] * 8 + [_fail(137)])
    outcome = await checker.check("the target", SUBMISSION_TAR)
    assert outcome.stage == "safeverify_resource"
    assert outcome.report is None


async def test_check_report_is_none_when_json_is_malformed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, _ = _checker(
        monkeypatch,
        [_ok()] * 8 + [_fail(1, "SafeVerify check failed.")],
        report="not json{",
    )
    outcome = await checker.check("the target", SUBMISSION_TAR)
    assert not outcome.ok
    assert outcome.report is None


async def test_check_report_is_none_when_too_large(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # safe_verify ran and rejected, but its --save report is too large to read
    # back (OutputLimitExceededError, MAX_READ_FILE_SIZE). The report is
    # supplementary offline data read after the verdict is decided, so an
    # oversized read degrades to None -- it must not change the verdict or error
    # the sample.
    checker, _ = _checker(
        monkeypatch,
        [_ok()] * 8 + [_fail(1, "SafeVerify check failed.")],
        report=_oversize_error(),
    )
    outcome = await checker.check("the target", SUBMISSION_TAR)
    assert not outcome.ok
    assert outcome.stage == "safeverify"
    assert outcome.report is None


async def test_check_raises_when_target_fails_to_compile(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Compile phase ok (5 execs), olean read ok, scorer clear+mkdir, then the
    # trusted-target compile (8th exec) fails -> our infra, so raise.
    checker, _ = _checker(monkeypatch, [_ok()] * 7 + [_fail(1, "bad spec")])
    with pytest.raises(RuntimeError, match="target spec"):
        await checker.check("the target", SUBMISSION_TAR)


async def test_check_rejects_when_submission_fails_to_compile(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # compile: clear, mkdir, untar ok, test entry ok, then `lake env lean` (5th
    # exec) fails -> a verdict on the agent's code.
    checker, _ = _checker(
        monkeypatch, [_ok(), _ok(), _ok(), _ok(), _fail(1, "unknown identifier")]
    )
    outcome = await checker.check("the target", SUBMISSION_TAR)
    assert not outcome.ok
    assert outcome.stage == "compile_submission"
    assert "unknown identifier" in outcome.detail


async def test_check_rejects_on_safeverify_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Both plain check failures and replay-time rejections (unsafe constant,
    # kernel type-check failure) exit nonzero: a rejection, not an infra error.
    checker, _ = _checker(
        monkeypatch, [_ok()] * 8 + [_fail(1, "SafeVerify check failed.")]
    )
    outcome = await checker.check("the target", SUBMISSION_TAR)
    assert not outcome.ok
    assert outcome.stage == "safeverify"


# --------------------------------------------------------------------------- #
# Attribution: failures of the *reference* code (clearing the workspace,       #
# compiling the trusted target spec) are our problem -> raise and error the    #
# sample. Failures of the agent's *submission* (unpacking it, its build, or    #
# safe_verify replaying it) are a verdict on the agent's code -> return a       #
# rejection so the agent is told, not error the sample. This holds for         #
# resource deaths (OOM/137, timeout) and decode errors alike.                  #
# --------------------------------------------------------------------------- #


async def test_check_raises_on_target_signal_death(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # 137 (OOM/SIGKILL) while compiling the *target* spec (8th exec, scorer
    # phase): reference side, so it is our infrastructure failing -> raise.
    checker, _ = _checker(monkeypatch, [_ok()] * 7 + [_fail(137)])
    with pytest.raises(RuntimeError, match="137"):
        await checker.check("the target", SUBMISSION_TAR)


async def test_check_raises_on_target_timeout(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A timeout compiling the trusted target spec is also reference-side: the
    # raised TimeoutError must propagate, not be swallowed into a verdict.
    checker, _ = _checker(monkeypatch, [_ok()] * 7 + [_timeout()])
    with pytest.raises(TimeoutError):
        await checker.check("the target", SUBMISSION_TAR)


async def test_check_rejects_on_submission_compile_signal_death(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # 137 compiling the *submission* (5th exec, compile phase): the agent's code
    # was too expensive to compile. A rejection the agent is told about, not an
    # errored sample.
    checker, _ = _checker(monkeypatch, [_ok(), _ok(), _ok(), _ok(), _fail(137)])
    outcome = await checker.check("the target", SUBMISSION_TAR)
    assert not outcome.ok
    assert outcome.stage == "compile_submission_resource"


async def test_check_rejects_on_submission_compile_timeout(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, _ = _checker(monkeypatch, [_ok(), _ok(), _ok(), _ok(), _timeout()])
    outcome = await checker.check("the target", SUBMISSION_TAR)
    assert not outcome.ok
    assert outcome.stage == "compile_submission_timeout"


async def test_check_rejects_on_safeverify_signal_death(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # 137 inside safe_verify replaying the submission (9th exec): safe_verify's
    # un-memoized rebuildExpr blew up on the agent's proof term. Agent-
    # attributable -> rejection, not a raise (deterministic; rerunning can't help).
    checker, _ = _checker(monkeypatch, [_ok()] * 8 + [_fail(137)])
    outcome = await checker.check("the target", SUBMISSION_TAR)
    assert not outcome.ok
    assert outcome.stage == "safeverify_resource"


async def test_check_rejects_on_safeverify_timeout(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, _ = _checker(monkeypatch, [_ok()] * 8 + [_timeout()])
    outcome = await checker.check("the target", SUBMISSION_TAR)
    assert not outcome.ok
    assert outcome.stage == "safeverify_timeout"


async def test_check_rejects_on_safeverify_decode_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A non-utf8 byte in safe_verify's output makes the provider raise
    # UnicodeDecodeError out of .exec(); that is the agent's submission output,
    # so it is a rejection, not a scaffold crash that errors the sample.
    checker, _ = _checker(monkeypatch, [_ok()] * 8 + [_decode_error()])
    outcome = await checker.check("the target", SUBMISSION_TAR)
    assert not outcome.ok
    assert outcome.stage == "safeverify_decode"


# --------------------------------------------------------------------------- #
# Scorer wiring                                                                #
# --------------------------------------------------------------------------- #


def _state() -> TaskState:
    return TaskState(
        model=ModelName("mockllm/model"),
        sample_id="t",
        epoch=1,
        input=SKETCH,
        messages=[],
        metadata={"sketch": SKETCH, "target_declarations": ["tgt"]},
    )


async def _score(
    checker: SafeVerifyChecker,
    tar: bytes,
    monkeypatch: pytest.MonkeyPatch,
) -> Score:
    monkeypatch.setattr(scorer_mod, "sandbox", lambda *a, **k: FakeSandbox(tar))
    result = await proof_scorer(checker)(_state(), Target(""))
    assert result is not None
    return result


async def test_scorer_hands_tar_to_checker_and_maps_correct(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    tar = b"the-submission-tar"
    checker = StubChecker(True)
    score = await _score(checker, tar, monkeypatch)
    assert score.value == CORRECT
    # The checker received the raw tar bytes read from the workspace sandbox.
    assert checker.calls == [tar]


async def test_scorer_incorrect_when_checker_rejects(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    score = await _score(StubChecker(False), b"tar", monkeypatch)
    assert score.value == INCORRECT


async def test_scorer_incorrect_when_submission_too_large(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # The agent's Submission/ is too large to read out of the sandbox
    # (read_submission_tar's read_file raises OutputLimitExceededError, the
    # MAX_READ_FILE_SIZE limit). That is agent-caused and deterministic, so the
    # scorer returns INCORRECT with an oversize stage rather than letting it error
    # the sample. With no tar there is nothing to verify -- the checker never runs.
    class OversizeSandbox:
        async def exec(self, cmd: list[str], **kwargs: object) -> ExecResult[str]:
            return ExecResult(success=True, returncode=0, stdout="", stderr="")

        async def read_file(self, file: str, text: bool = True) -> bytes:
            raise OutputLimitExceededError(limit_str="100 MiB", truncated_output=None)

    monkeypatch.setattr(scorer_mod, "sandbox", lambda *a, **k: OversizeSandbox())
    checker = StubChecker(True)
    score = await proof_scorer(checker)(_state(), Target(""))
    assert score is not None
    assert score.value == INCORRECT
    assert score.metadata is not None
    assert score.metadata["stage"] == "submission_oversize"
    # No tar to hand it, so the checker was never called.
    assert checker.calls == []


async def test_scorer_metadata_has_no_tree(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Score.metadata carries only the small verdict/report -- never the tree
    # (which would bloat the event log across up to max_attempts attempts), and
    # no answer (purely cosmetic; the full tree lives on sample metadata).
    report: list[dict[str, object]] = [{"failureMode": None}]
    score = await _score(StubChecker(True, report=report), b"tar", monkeypatch)
    assert score.answer is None
    assert score.metadata is not None
    assert set(score.metadata) == {"stage", "safeverify_report"}
    assert score.metadata["stage"] == "stub"
    assert score.metadata["safeverify_report"] == report


async def test_scorer_records_submission_tree_on_sample_metadata(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # The scorer builds the display tree from the same tar it reads and stores it
    # on *sample* metadata (so the log viewer / extract_plaintext can render it),
    # not on Score.metadata. This is the reliable capture point -- the scorer runs
    # even when a limit terminated the agent, unlike anything after the solver's
    # run(). build_tree nests helper subdirs.
    import io
    import tarfile

    buf = io.BytesIO()
    files = {
        "Spec.lean": "import X\ntheorem tgt := by sorry\n",
        "Helpers/Aux.lean": "theorem aux := trivial\n",
    }
    with tarfile.open(fileobj=buf, mode="w") as tf:
        for name, content in files.items():
            data = content.encode()
            info = tarfile.TarInfo(name)
            info.size = len(data)
            tf.addfile(info, io.BytesIO(data))

    state = _state()
    monkeypatch.setattr(scorer_mod, "sandbox", lambda *a, **k: FakeSandbox(buf.getvalue()))
    await proof_scorer(StubChecker(True))(state, Target(""))

    assert state.metadata["submission_contents"] == {
        "Spec.lean": "import X\ntheorem tgt := by sorry\n",
        "Helpers": {"Aux.lean": "theorem aux := trivial\n"},
    }


async def test_scorer_writes_attempt_sidecar(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Per attempt, the scored Submission/ tar is written to an attempt-indexed
    # sidecar under <logdir>/artifacts/<uuid>/. Stub the private sample_active so
    # the log dir resolves to tmp_path.
    import inspect_ai.log._samples as samples_mod

    monkeypatch.setattr(
        samples_mod,
        "sample_active",
        lambda: SimpleNamespace(log_location=str(tmp_path / "run.eval")),
    )
    tar = b"the-submission-tar"
    await _score(StubChecker(True), tar, monkeypatch)
    sidecars = list((tmp_path / "artifacts").rglob("attempt-*.tar"))
    assert len(sidecars) == 1
    # The sidecar holds the exact tar bytes that were scored.
    assert sidecars[0].read_bytes() == tar
