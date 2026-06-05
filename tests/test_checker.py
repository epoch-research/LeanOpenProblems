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
    def __init__(self, ok: bool) -> None:
        self._ok = ok

    async def check(self, target: str, submission: str) -> CheckOutcome:
        return CheckOutcome(ok=self._ok, stage="stub", detail="stub outcome")


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
    """A scorer-sandbox stub: records writes, returns/raises scripted steps."""

    def __init__(self, results: list[Step]) -> None:
        self._results = list(results)
        self.written: dict[str, str] = {}
        self.commands: list[list[str]] = []

    async def write_file(self, file: str, contents: str) -> None:
        self.written[file] = contents

    async def exec(self, cmd: list[str], **kwargs: object) -> ExecResult[str]:
        self.commands.append(cmd)
        step = self._results.pop(0)
        if isinstance(step, BaseException):
            raise step
        return step


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
) -> tuple[SandboxSafeVerify, ScriptedSandbox]:
    sb = ScriptedSandbox(results)
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
    assert len(sb.written) == 2
    assert len(sb.commands) == 4
    assert sb.commands[0][:2] == ["rm", "-rf"]


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
    # The flag precedes the two positional olean paths.
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
