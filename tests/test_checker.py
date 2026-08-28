"""Tests for the Comparator checker's exec orchestration and the scorer wiring.

``SandboxComparator`` drives one trusted ``comparator`` sandbox. Per check it:
resets the workspace (a reference step), writes ``run/Challenge.lean`` (the
sample spec verbatim), ``run/Solution.lean`` (the agent's Spec.lean, extracted
host-side from the tar), and ``run/config.json``, then runs the comparator
binary under ``lake env``. Exit 0 accepts. Attribution keys off comparator's
exit code rather than its bounded, submission-controlled output: once the
comparator starts, every nonzero exit is a verdict on the submission. Failures
in the separate trusted reset and staging operations still raise.

A fake sandbox scripts the exec/write sequence to verify that mapping. The
scorer tests use a stub checker and a fake workspace sandbox to verify the
``Submission/`` tar is collected, the declared claim is read from the store,
and both are handed to the checker.
"""

from __future__ import annotations

import io
import json
import tarfile
from pathlib import Path
from types import SimpleNamespace
from typing import cast

import pytest
from inspect_ai.model import ModelName
from inspect_ai.scorer import CORRECT, INCORRECT, Score, Target
from inspect_ai.solver import TaskState
from inspect_ai.util import ExecResult, OutputLimitExceededError

import apn.checker as checker_mod
import apn.scorer as scorer_mod
from apn.checker import (
    CHALLENGE_PATH,
    COMPARATOR_USER,
    CONFIG_PATH,
    RESET_SCRIPT,
    RUN_DIR,
    SOLUTION_PATH,
    CheckOutcome,
    ProofChecker,
    SandboxComparator,
    extract_entry,
)
from apn.scorer import CLAIM_STORE_KEY, proof_scorer

SPEC = "import Mathlib\ntheorem tgt : True := by sorry\ntheorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"


def _tar_of(files: dict[str, str]) -> bytes:
    """Pack ``{relative path: contents}`` into the tar the checker consumes
    (members relative to ``Submission/``, i.e. ``./Spec.lean``)."""
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w") as tf:
        for name, content in files.items():
            data = content.encode()
            info = tarfile.TarInfo(name)
            info.size = len(data)
            tf.addfile(info, io.BytesIO(data))
    return buf.getvalue()


SUBMISSION_TAR = _tar_of({"./Spec.lean": "theorem tgt : True := trivial\n"})


class StubChecker:
    def __init__(self, ok: bool) -> None:
        self._ok = ok
        self.calls: list[tuple[str, bytes, str, str]] = []

    async def check(
        self, spec: str, submission_tar: bytes, decl: str, claim: str
    ) -> CheckOutcome:
        self.calls.append((spec, submission_tar, decl, claim))
        return CheckOutcome(ok=self._ok, stage="stub", detail="stub outcome")


class FakeStore:
    """Minimal stand-in for Inspect's per-sample ``store()``."""

    def __init__(self, initial: dict[str, object] | None = None) -> None:
        self._data: dict[str, object] = dict(initial or {})

    def get(self, key: str, default: object = None) -> object:
        return self._data.get(key, default)

    def set(self, key: str, value: object) -> None:
        self._data[key] = value


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
# extract_entry (host-side tar handling)                                       #
# --------------------------------------------------------------------------- #
def test_extract_entry_reads_spec() -> None:
    assert extract_entry(_tar_of({"./Spec.lean": "X"})) == "X"
    # A bare (no ./) member name is accepted too.
    assert extract_entry(_tar_of({"Spec.lean": "Y"})) == "Y"


def test_extract_entry_ignores_helper_files() -> None:
    tar = _tar_of({"./Spec.lean": "the spec", "./Helpers/Aux.lean": "aux"})
    assert extract_entry(tar) == "the spec"


def test_extract_entry_missing_member_is_none() -> None:
    assert extract_entry(_tar_of({"./Other.lean": "x"})) is None
    assert extract_entry(_tar_of({})) is None


def test_extract_entry_malformed_tar_is_none() -> None:
    assert extract_entry(b"not a tar at all") is None


def test_extract_entry_non_utf8_is_none() -> None:
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w") as tf:
        data = b"\xff\xfe not utf8"
        info = tarfile.TarInfo("./Spec.lean")
        info.size = len(data)
        tf.addfile(info, io.BytesIO(data))
    assert extract_entry(buf.getvalue()) is None


def test_extract_entry_oversize_member_is_none(monkeypatch: pytest.MonkeyPatch) -> None:
    # A member whose header size exceeds the cap is rejected on the size field
    # before any read. Shrink the cap so the fixture stays small.
    monkeypatch.setattr(checker_mod, "MAX_ENTRY_BYTES", 8)
    assert extract_entry(_tar_of({"./Spec.lean": "x" * 32})) is None
    assert extract_entry(_tar_of({"./Spec.lean": "tiny"})) == "tiny"


# --------------------------------------------------------------------------- #
# SandboxComparator exec orchestration                                         #
# --------------------------------------------------------------------------- #
# The checker's trusted staging reset (recreate run/ before writing inputs).
STAGING_RESET = ["sh", "-c", f"rm -rf {RUN_DIR} && mkdir {RUN_DIR}"]


class ScriptedSandbox:
    """A stub for the comparator sandbox: records writes/execs and returns (or
    raises) a scripted result for the .lake reset exec, the staging reset exec,
    then the comparator exec."""

    def __init__(
        self,
        reset: ExecResult[str] | None = None,
        staging: ExecResult[str] | None = None,
        comparator: ExecResult[str] | BaseException | None = None,
    ) -> None:
        self._reset = reset if reset is not None else ExecResult(True, 0, "", "")
        self._staging = staging if staging is not None else ExecResult(True, 0, "", "")
        self._comparator = comparator
        self.written: dict[str, object] = {}
        self.writes: list[tuple[str, object]] = []
        self.commands: list[list[str]] = []
        self.exec_kwargs: list[dict[str, object]] = []

    async def write_file(self, file: str, contents: object) -> None:
        self.written[file] = contents
        self.writes.append((file, contents))

    async def exec(self, cmd: list[str], **kwargs: object) -> ExecResult[str]:
        self.commands.append(cmd)
        self.exec_kwargs.append(kwargs)
        if cmd == [RESET_SCRIPT]:
            return self._reset
        if cmd == STAGING_RESET:
            return self._staging
        step = self._comparator
        if isinstance(step, BaseException):
            raise step
        assert step is not None, f"unexpected exec: {cmd}"
        return step


def _ok(stdout: str = "", stderr: str = "") -> ExecResult[str]:
    return ExecResult(success=True, returncode=0, stdout=stdout, stderr=stderr)


def _fail(returncode: int, stdout: str = "", stderr: str = "") -> ExecResult[str]:
    return ExecResult(success=False, returncode=returncode, stdout=stdout, stderr=stderr)


_ACCEPT_OUT = "Building Challenge\nBuilding Solution\nYour solution is okay!"


def _checker(
    monkeypatch: pytest.MonkeyPatch,
    reset: ExecResult[str] | None = None,
    staging: ExecResult[str] | None = None,
    comparator: ExecResult[str] | BaseException | None = None,
) -> tuple[SandboxComparator, ScriptedSandbox]:
    sb = ScriptedSandbox(reset=reset, staging=staging, comparator=comparator)
    monkeypatch.setattr(checker_mod, "sandbox", lambda *a, **k: sb)
    return SandboxComparator(), sb


async def test_check_accepts_on_exit_zero(monkeypatch: pytest.MonkeyPatch) -> None:
    checker, sb = _checker(monkeypatch, comparator=_ok(_ACCEPT_OUT))
    outcome = await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    assert outcome.ok
    assert outcome.stage == "comparator"
    # .lake reset, staging reset, then the comparator invocation.
    assert sb.commands[0] == [RESET_SCRIPT]
    assert sb.commands[1] == STAGING_RESET
    assert sb.commands[2][:3] == ["lake", "env", checker_mod.COMPARATOR_BIN]


async def test_check_stages_challenge_solution_config(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, sb = _checker(monkeypatch, comparator=_ok(_ACCEPT_OUT))
    await checker.check("THE SPEC", _tar_of({"./Spec.lean": "THE SOLUTION"}),
                        decl="Foo.bar", claim="disproof")
    # Challenge = the spec verbatim; Solution = the extracted Spec.lean.
    assert sb.written[CHALLENGE_PATH] == "THE SPEC"
    assert sb.written[SOLUTION_PATH] == "THE SOLUTION"
    # The config targets the .disproof theorem for a disproof claim.
    config = json.loads(cast(str, sb.written[CONFIG_PATH]))
    assert config["theorem_names"] == ["Foo.bar.disproof"]
    assert config["challenge_module"] == "Challenge"
    assert config["solution_module"] == "Solution"
    assert config["permitted_axioms"] == ["propext", "Classical.choice", "Quot.sound"]


async def test_check_execs_drop_to_comparator_user(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # The comparator image stays root for Inspect's benefit, so the privilege
    # drop lives on the exec calls: every command the checker runs in the
    # comparator sandbox must carry user=COMPARATOR_USER.
    checker, sb = _checker(monkeypatch, comparator=_ok(_ACCEPT_OUT))
    await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    assert sb.commands == [[RESET_SCRIPT], STAGING_RESET,
                           ["lake", "env", checker_mod.COMPARATOR_BIN, CONFIG_PATH]]
    assert [kw.get("user") for kw in sb.exec_kwargs] == [COMPARATOR_USER] * 3


async def test_check_proof_claim_targets_bare_decl(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, sb = _checker(monkeypatch, comparator=_ok(_ACCEPT_OUT))
    await checker.check(SPEC, SUBMISSION_TAR, decl="Foo.bar", claim="proof")
    assert json.loads(cast(str, sb.written[CONFIG_PATH]))["theorem_names"] == ["Foo.bar"]


async def test_check_rejects_missing_entry_before_touching_sandbox(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A submission tar with no Spec.lean is a verdict, decided host-side: the
    # sandbox is never touched (no reset, no comparator run).
    checker, sb = _checker(monkeypatch, comparator=_ok(_ACCEPT_OUT))
    outcome = await checker.check(SPEC, _tar_of({"./Other.lean": "x"}),
                                  decl="tgt", claim="proof")
    assert not outcome.ok
    assert outcome.stage == "entry_missing"
    assert sb.commands == []


async def test_check_rejects_when_comparator_failed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Any nonzero comparator exit is a verdict on the submission.
    out = (
        "Building Challenge\nBuilding Solution\n"
        "uncaught exception: Illegal axiom detected: 'sorryAx'"
    )
    checker, _ = _checker(monkeypatch, comparator=_fail(1, out))
    outcome = await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    assert not outcome.ok
    assert outcome.stage == "comparator"


async def test_check_rejects_without_relying_on_phase_marker(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Output is bounded and submission-controlled, so even a failure with no
    # solution marker is classified solely by the comparator's nonzero exit.
    out = "Building Challenge\nerror: challenge spec failed to build"
    checker, _ = _checker(monkeypatch, comparator=_fail(1, out))
    outcome = await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    assert not outcome.ok
    assert outcome.stage == "comparator"


async def test_check_raises_when_reset_fails(monkeypatch: pytest.MonkeyPatch) -> None:
    # The .lake reset is a reference step; its failure is our infrastructure.
    checker, sb = _checker(monkeypatch, reset=_fail(1, stderr="reset boom"),
                           comparator=_ok(_ACCEPT_OUT))
    with pytest.raises(RuntimeError, match=r"\.lake reset failed"):
        await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    # Nothing ran past the failed reset.
    assert sb.commands == [[RESET_SCRIPT]]


async def test_check_raises_when_staging_reset_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Recreating run/ is likewise a reference step.
    checker, sb = _checker(monkeypatch, staging=_fail(1, stderr="mkdir boom"),
                           comparator=_ok(_ACCEPT_OUT))
    with pytest.raises(RuntimeError, match="staging reset failed"):
        await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    # Nothing ran past the failed staging reset (and nothing was staged).
    assert sb.commands == [[RESET_SCRIPT], STAGING_RESET]
    assert sb.written == {}


async def test_check_maps_resource_death(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A signal-style exit is a resource-stage rejection even when the bounded
    # output provides no indication of Comparator's internal phase.
    checker, _ = _checker(monkeypatch, comparator=_fail(137))
    outcome = await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    assert not outcome.ok
    assert outcome.stage == "comparator_resource"


async def test_check_maps_timeout(monkeypatch: pytest.MonkeyPatch) -> None:
    checker, _ = _checker(monkeypatch, comparator=TimeoutError("timed out"))
    outcome = await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    assert not outcome.ok
    assert outcome.stage == "comparator_timeout"


async def test_check_maps_decode_error(monkeypatch: pytest.MonkeyPatch) -> None:
    exc = UnicodeDecodeError("utf-8", b"\xff", 0, 1, "invalid start byte")
    checker, _ = _checker(monkeypatch, comparator=exc)
    outcome = await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    assert not outcome.ok
    assert outcome.stage == "comparator"


async def test_check_maps_output_limit(monkeypatch: pytest.MonkeyPatch) -> None:
    # A stream past Inspect's exec output cap is submission-controlled (the
    # trusted phases print a handful of lines), so it scores INCORRECT rather
    # than raising -- printing 10 MiB must not error the sample.
    exc = OutputLimitExceededError(limit_str="10 MiB", truncated_output=None)
    checker, _ = _checker(monkeypatch, comparator=exc)
    outcome = await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    assert not outcome.ok
    assert outcome.stage == "comparator_output_limit"


# --------------------------------------------------------------------------- #
# Scorer wiring                                                                #
# --------------------------------------------------------------------------- #
def _state(store: FakeStore) -> TaskState:
    st = TaskState(
        model=ModelName("mockllm/model"),
        sample_id="t",
        epoch=1,
        input=SPEC,
        messages=[],
        metadata={"sketch": SPEC, "decl_name": "tgt"},
    )
    return st


async def _score(
    checker: ProofChecker,
    tar: bytes,
    monkeypatch: pytest.MonkeyPatch,
    store: FakeStore | None = None,
) -> Score:
    store = store if store is not None else FakeStore()
    monkeypatch.setattr(scorer_mod, "sandbox", lambda *a, **k: FakeSandbox(tar))
    monkeypatch.setattr(scorer_mod, "store", lambda: store)
    result = await proof_scorer(checker)(_state(store), Target(""))
    assert result is not None
    return result


async def test_scorer_hands_spec_tar_decl_claim_to_checker(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    tar = _tar_of({"./Spec.lean": "sol"})
    checker = StubChecker(True)
    store = FakeStore({CLAIM_STORE_KEY: "disproof"})
    score = await _score(checker, tar, monkeypatch, store)
    assert score.value == CORRECT
    # The checker got the spec, the raw tar, the decl name, and the claim.
    (spec, got_tar, decl, claim) = checker.calls[0]
    assert spec == SPEC
    assert got_tar == tar
    assert decl == "tgt"
    assert claim == "disproof"


async def test_scorer_defaults_claim_to_proof(monkeypatch: pytest.MonkeyPatch) -> None:
    # A sample scored without ever recording a claim (e.g. it hit its limits)
    # defaults to "proof".
    checker = StubChecker(False)
    score = await _score(checker, _tar_of({"./Spec.lean": "x"}), monkeypatch)
    assert checker.calls[0][3] == "proof"
    assert score.value == INCORRECT


async def test_scorer_incorrect_when_checker_rejects(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    score = await _score(StubChecker(False), _tar_of({"./Spec.lean": "x"}), monkeypatch)
    assert score.value == INCORRECT


async def test_scorer_incorrect_when_submission_too_large(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # The agent's Submission/ is too large to read out of the sandbox
    # (read_submission_tar's read_file raises OutputLimitExceededError). That is
    # agent-caused and deterministic, so the scorer returns INCORRECT with an
    # oversize stage rather than letting it error the sample. With no tar there
    # is nothing to verify -- the checker never runs.
    class OversizeSandbox:
        async def exec(self, cmd: list[str], **kwargs: object) -> ExecResult[str]:
            return ExecResult(success=True, returncode=0, stdout="", stderr="")

        async def read_file(self, file: str, text: bool = True) -> bytes:
            raise OutputLimitExceededError(limit_str="100 MiB", truncated_output=None)

    store = FakeStore()
    monkeypatch.setattr(scorer_mod, "sandbox", lambda *a, **k: OversizeSandbox())
    monkeypatch.setattr(scorer_mod, "store", lambda: store)
    checker = StubChecker(True)
    score = await proof_scorer(checker)(_state(store), Target(""))
    assert score is not None
    assert score.value == INCORRECT
    assert score.metadata is not None
    assert score.metadata["stage"] == "submission_oversize"
    assert checker.calls == []


async def test_scorer_metadata_shape(monkeypatch: pytest.MonkeyPatch) -> None:
    # Score.metadata carries the verdict/verifier fields and the claim -- never
    # the tree (which lives on sample metadata) and no answer.
    score = await _score(StubChecker(True), _tar_of({"./Spec.lean": "x"}), monkeypatch)
    assert score.answer is None
    assert score.metadata is not None
    assert set(score.metadata) == {"stage", "claim", "verifier_output"}
    assert score.metadata["stage"] == "stub"


async def test_scorer_records_submission_tree_on_sample_metadata(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # The scorer builds the display tree from the same tar it reads and stores it
    # on *sample* metadata (so the log viewer / extract_plaintext can render it),
    # not on Score.metadata.
    tar = _tar_of(
        {"Spec.lean": "import X\ntheorem tgt := by sorry\n", "Helpers/Aux.lean": "theorem aux := trivial\n"}
    )
    store = FakeStore()
    state = _state(store)
    monkeypatch.setattr(scorer_mod, "sandbox", lambda *a, **k: FakeSandbox(tar))
    monkeypatch.setattr(scorer_mod, "store", lambda: store)
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
    tar = _tar_of({"./Spec.lean": "the-submission"})
    await _score(StubChecker(True), tar, monkeypatch)
    sidecars = list((tmp_path / "artifacts").rglob("attempt-*.tar"))
    assert len(sidecars) == 1
    assert sidecars[0].read_bytes() == tar
