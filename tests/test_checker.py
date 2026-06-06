"""Tests for the SafeVerify checker's exec orchestration and the scorer wiring.

``SandboxSafeVerify`` runs three commands in the scorer sandbox (compile
target, compile submission, run ``safe_verify``); here a fake sandbox scripts
their exit codes to verify the verdict mapping. The real ``safe_verify`` exe is
validated against the toolchain. The scorer tests use a stub checker and a fake
workspace sandbox to verify the proof file is read and mapped to
CORRECT/INCORRECT.
"""

from __future__ import annotations

import pytest
from inspect_ai.model import ModelName
from inspect_ai.scorer import CORRECT, INCORRECT, Score, Target
from inspect_ai.solver import TaskState
from inspect_ai.util import ExecResult

import apn.checker as checker_mod
import apn.scorer as scorer_mod
from apn.checker import CheckOutcome, SafeVerifyChecker, SandboxSafeVerify
from apn.scorer import proof_scorer

SKETCH = "import Mathlib\ntheorem tgt : True := by sorry\n"


class StubChecker:
    def __init__(
        self, ok: bool, report: list[dict[str, object]] | None = None
    ) -> None:
        self._ok = ok
        self._report = report

    async def check(self, target: str, submission: str) -> CheckOutcome:
        return CheckOutcome(
            ok=self._ok, stage="stub", detail="stub outcome", report=self._report
        )


class FakeSandbox:
    """Stands in for the sample's workspace sandbox, returning a fixed file."""

    def __init__(self, content: str) -> None:
        self._content = content

    async def read_file(self, file: str, text: bool = True) -> str:
        return self._content


# --------------------------------------------------------------------------- #
# SandboxSafeVerify exec orchestration                                         #
# --------------------------------------------------------------------------- #


# A scripted step is either an ExecResult the fake exec returns, or an
# exception the fake exec raises -- the sandbox provider *raises* (rather than
# returns) on a timeout (TimeoutError) and on an undecodable output byte
# (UnicodeDecodeError), so the checker has to catch those at the .exec() call.
Step = ExecResult[str] | BaseException


class ScriptedSandbox:
    """A scorer-sandbox stub: records writes, returns/raises scripted steps.

    ``report`` scripts the safe_verify ``--save`` JSON the checker reads back:
    a string is returned from ``read_file``, ``None`` (the default) raises
    ``FileNotFoundError`` (safe_verify wrote nothing).
    """

    def __init__(self, results: list[Step], report: str | None = None) -> None:
        self._results = list(results)
        self._report = report
        self.written: dict[str, str] = {}
        # Ordered log of every write -- ``written`` collapses repeated writes to
        # the same path, but the target and submission deliberately share one
        # source path, so the sequence matters.
        self.writes: list[tuple[str, str]] = []
        self.commands: list[list[str]] = []
        self.reads: list[str] = []

    async def write_file(self, file: str, contents: str) -> None:
        self.written[file] = contents
        self.writes.append((file, contents))

    async def exec(self, cmd: list[str], **kwargs: object) -> ExecResult[str]:
        self.commands.append(cmd)
        step = self._results.pop(0)
        if isinstance(step, BaseException):
            raise step
        return step

    async def read_file(self, file: str, text: bool = True) -> str:
        self.reads.append(file)
        if self._report is None:
            raise FileNotFoundError(file)
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


def _checker(
    monkeypatch: pytest.MonkeyPatch,
    results: list[Step],
    allow_disproofs: bool = True,
    report: str | None = None,
) -> tuple[SandboxSafeVerify, ScriptedSandbox]:
    sb = ScriptedSandbox(results, report=report)
    monkeypatch.setattr(checker_mod, "sandbox", lambda *a, **k: sb)
    return SandboxSafeVerify(allow_disproofs=allow_disproofs), sb


async def test_check_accepts_when_all_steps_pass(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Each call begins with a workspace-clear exec, then compiles target,
    # compiles submission, runs safe_verify -- four commands in the happy path.
    checker, sb = _checker(
        monkeypatch, [_ok(), _ok(), _ok(), _ok("SafeVerify check passed.")]
    )
    outcome = await checker.check("the target", "the submission")
    assert outcome.ok
    assert outcome.stage == "safeverify"
    # Two source writes (target, then submission), then four commands:
    # clear, compile target, compile submission, safe_verify.
    assert len(sb.writes) == 2
    assert len(sb.commands) == 4
    assert sb.commands[0][:2] == ["rm", "-rf"]


async def test_check_compiles_both_from_same_source_path(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Load-bearing for private-name matching: the target and submission must
    # compile from the SAME source path so Lean gives them the same module name
    # (otherwise a pattern-matching def's private `_private.<module>.0.a.match_1`
    # lemmas mangle differently and SafeVerify's exact-name match rejects a
    # faithful proof). See SandboxSafeVerify.check's comment.
    checker, sb = _checker(
        monkeypatch, [_ok(), _ok(), _ok(), _ok("SafeVerify check passed.")]
    )
    await checker.check("THE TARGET", "THE SUBMISSION")
    # Target written first, then the submission overwrites it -- both at SOURCE.
    assert sb.writes == [
        (checker_mod.SOURCE, "THE TARGET"),
        (checker_mod.SOURCE, "THE SUBMISSION"),
    ]
    # Each compile reads that one shared source but emits a distinct olean.
    target_compile, submission_compile = sb.commands[1], sb.commands[2]
    assert target_compile[-2:] == [checker_mod.TARGET_OLEAN, checker_mod.SOURCE]
    assert submission_compile[-2:] == [checker_mod.SUBMISSION_OLEAN, checker_mod.SOURCE]


async def test_check_passes_disproofs_flag_to_safe_verify(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # By default the agent may disprove a conjecture, so safe_verify is invoked
    # with --disproofs (it then accepts foo OR foo.disproof for each target).
    checker, sb = _checker(
        monkeypatch, [_ok(), _ok(), _ok(), _ok("SafeVerify check passed.")]
    )
    outcome = await checker.check("the target", "the submission")
    assert outcome.ok
    safe_verify_cmd = sb.commands[3]
    assert "--disproofs" in safe_verify_cmd
    # --save requests the JSON report; the two olean paths stay positional last.
    assert "--save" in safe_verify_cmd
    assert safe_verify_cmd[-2].endswith("target.olean")
    assert safe_verify_cmd[-1].endswith("submission.olean")


async def test_check_omits_disproofs_flag_when_disabled(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, sb = _checker(
        monkeypatch,
        [_ok(), _ok(), _ok(), _ok("SafeVerify check passed.")],
        allow_disproofs=False,
    )
    await checker.check("the target", "the submission")
    assert "--disproofs" not in sb.commands[3]


async def test_check_attaches_safeverify_report(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # safe_verify's --save JSON is read back and attached to the outcome.
    report = '[{"targetInfo": {"constInfo": {"kind": "theorem"}}, "failureMode": null}]'
    checker, sb = _checker(
        monkeypatch,
        [_ok(), _ok(), _ok(), _ok("SafeVerify check passed.")],
        report=report,
    )
    outcome = await checker.check("the target", "the submission")
    assert outcome.ok
    assert outcome.report == [
        {"targetInfo": {"constInfo": {"kind": "theorem"}}, "failureMode": None}
    ]
    assert sb.reads == [checker_mod.REPORT_PATH]


async def test_check_report_is_none_when_safe_verify_wrote_nothing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A resource death can leave no report file; a missing read is not an error.
    checker, _ = _checker(monkeypatch, [_ok(), _ok(), _ok(), _fail(137)])
    outcome = await checker.check("the target", "the submission")
    assert outcome.stage == "safeverify_resource"
    assert outcome.report is None


async def test_check_report_is_none_when_json_is_malformed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, _ = _checker(
        monkeypatch,
        [_ok(), _ok(), _ok(), _fail(1, "SafeVerify check failed.")],
        report="not json{",
    )
    outcome = await checker.check("the target", "the submission")
    assert not outcome.ok
    assert outcome.report is None


async def test_check_raises_when_target_fails_to_compile(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, _ = _checker(monkeypatch, [_ok(), _fail(1, "bad spec")])
    with pytest.raises(RuntimeError, match="target spec"):
        await checker.check("the target", "the submission")


async def test_check_rejects_when_submission_fails_to_compile(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, _ = _checker(
        monkeypatch, [_ok(), _ok(), _fail(1, "unknown identifier")]
    )
    outcome = await checker.check("the target", "the submission")
    assert not outcome.ok
    assert outcome.stage == "compile_submission"
    assert "unknown identifier" in outcome.detail


async def test_check_rejects_on_safeverify_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Both plain check failures and replay-time rejections (unsafe constant,
    # kernel type-check failure) exit nonzero: a rejection, not an infra error.
    checker, _ = _checker(
        monkeypatch, [_ok(), _ok(), _ok(), _fail(1, "SafeVerify check failed.")]
    )
    outcome = await checker.check("the target", "the submission")
    assert not outcome.ok
    assert outcome.stage == "safeverify"


# --------------------------------------------------------------------------- #
# Attribution: failures of the *reference* code (compiling the trusted target  #
# spec) are our problem -> raise and error the sample. Failures of the agent's #
# *submission* (its compile, or safe_verify replaying it) are a verdict on the #
# agent's code -> return a rejection so the agent is told, not error the       #
# sample. This holds for resource deaths (OOM/137, timeout) and decode errors  #
# alike, which is exactly where the old "raise on any signal, anywhere" was    #
# wrong: those deaths were almost always the agent's expensive proof term.     #
# --------------------------------------------------------------------------- #


async def test_check_raises_on_target_signal_death(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # 137 (OOM/SIGKILL) while compiling the *target* spec: reference side, so
    # it is our infrastructure failing -> raise, never a verdict.
    checker, _ = _checker(monkeypatch, [_ok(), _fail(137)])
    with pytest.raises(RuntimeError, match="137"):
        await checker.check("the target", "the submission")


async def test_check_raises_on_target_timeout(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A timeout compiling the trusted target spec is also reference-side: the
    # raised TimeoutError must propagate, not be swallowed into a verdict.
    checker, _ = _checker(monkeypatch, [_ok(), _timeout()])
    with pytest.raises(TimeoutError):
        await checker.check("the target", "the submission")


async def test_check_rejects_on_submission_compile_signal_death(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # 137 compiling the *submission*: the agent's code was too expensive to
    # compile. A rejection the agent is told about, not an errored sample.
    checker, _ = _checker(monkeypatch, [_ok(), _ok(), _fail(137)])
    outcome = await checker.check("the target", "the submission")
    assert not outcome.ok
    assert outcome.stage == "compile_submission_resource"


async def test_check_rejects_on_submission_compile_timeout(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, _ = _checker(monkeypatch, [_ok(), _ok(), _timeout()])
    outcome = await checker.check("the target", "the submission")
    assert not outcome.ok
    assert outcome.stage == "compile_submission_timeout"


async def test_check_rejects_on_safeverify_signal_death(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # 137 inside safe_verify replaying the submission: safe_verify's un-memoized
    # rebuildExpr blew up on the agent's proof term. Agent-attributable ->
    # rejection, not a raise (it is deterministic; rerunning cannot help).
    checker, _ = _checker(monkeypatch, [_ok(), _ok(), _ok(), _fail(137)])
    outcome = await checker.check("the target", "the submission")
    assert not outcome.ok
    assert outcome.stage == "safeverify_resource"


async def test_check_rejects_on_safeverify_timeout(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, _ = _checker(monkeypatch, [_ok(), _ok(), _ok(), _timeout()])
    outcome = await checker.check("the target", "the submission")
    assert not outcome.ok
    assert outcome.stage == "safeverify_timeout"


async def test_check_rejects_on_safeverify_decode_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A non-utf8 byte in safe_verify's output makes the provider raise
    # UnicodeDecodeError out of .exec(); that is the agent's submission output,
    # so it is a rejection, not a scaffold crash that errors the sample.
    checker, _ = _checker(monkeypatch, [_ok(), _ok(), _ok(), _decode_error()])
    outcome = await checker.check("the target", "the submission")
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
    checker: SafeVerifyChecker, submission: str, monkeypatch: pytest.MonkeyPatch
) -> Score:
    monkeypatch.setattr(scorer_mod, "sandbox", lambda *a, **k: FakeSandbox(submission))
    result = await proof_scorer(checker)(_state(), Target(""))
    assert result is not None
    return result


async def test_scorer_correct_when_checker_accepts(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    score = await _score(StubChecker(True), "the proof", monkeypatch)
    assert score.value == CORRECT
    assert score.answer == "the proof"


async def test_scorer_incorrect_when_checker_rejects(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    score = await _score(StubChecker(False), "the proof", monkeypatch)
    assert score.value == INCORRECT


async def test_scorer_records_stage_and_report_in_metadata(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    report: list[dict[str, object]] = [{"failureMode": None}]
    score = await _score(StubChecker(True, report=report), "the proof", monkeypatch)
    assert score.metadata is not None
    assert score.metadata["stage"] == "stub"
    assert score.metadata["safeverify_report"] == report
