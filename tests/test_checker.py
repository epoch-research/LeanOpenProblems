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


class ScriptedSandbox:
    """A scorer-sandbox stub: records writes, returns scripted exec results."""

    def __init__(self, results: list[ExecResult[str]]) -> None:
        self._results = list(results)
        self.written: dict[str, str] = {}
        self.commands: list[list[str]] = []

    async def write_file(self, file: str, contents: str) -> None:
        self.written[file] = contents

    async def exec(self, cmd: list[str], **kwargs: object) -> ExecResult[str]:
        self.commands.append(cmd)
        return self._results.pop(0)


def _ok(stderr: str = "") -> ExecResult[str]:
    return ExecResult(success=True, returncode=0, stdout="", stderr=stderr)


def _fail(returncode: int, stderr: str = "") -> ExecResult[str]:
    return ExecResult(success=False, returncode=returncode, stdout="", stderr=stderr)


def _checker(
    monkeypatch: pytest.MonkeyPatch, results: list[ExecResult[str]]
) -> tuple[SandboxSafeVerify, ScriptedSandbox]:
    sb = ScriptedSandbox(results)
    monkeypatch.setattr(checker_mod, "sandbox", lambda *a, **k: sb)
    return SandboxSafeVerify(), sb


async def test_check_accepts_when_all_steps_pass(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, sb = _checker(
        monkeypatch, [_ok(), _ok(), _ok("SafeVerify check passed.")]
    )
    outcome = await checker.check("the target", "the submission")
    assert outcome.ok
    assert outcome.stage == "safeverify"
    # Both files were written into the score dir, three commands ran.
    assert len(sb.written) == 2
    assert len(sb.commands) == 3


async def test_check_raises_when_target_fails_to_compile(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, _ = _checker(monkeypatch, [_fail(1, "bad spec")])
    with pytest.raises(RuntimeError, match="target spec"):
        await checker.check("the target", "the submission")


async def test_check_rejects_when_submission_fails_to_compile(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, _ = _checker(monkeypatch, [_ok(), _fail(1, "unknown identifier")])
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
        monkeypatch, [_ok(), _ok(), _fail(1, "SafeVerify check failed.")]
    )
    outcome = await checker.check("the target", "the submission")
    assert not outcome.ok
    assert outcome.stage == "safeverify"


async def test_check_raises_on_signal_death(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Exit 137 = SIGKILL (e.g. the OOM killer): not a verdict, so it must
    # raise rather than score the proof INCORRECT -- wherever it happens.
    checker, _ = _checker(monkeypatch, [_ok(), _ok(), _fail(137)])
    with pytest.raises(RuntimeError, match="137"):
        await checker.check("the target", "the submission")
    checker, _ = _checker(monkeypatch, [_ok(), _fail(137)])
    with pytest.raises(RuntimeError, match="137"):
        await checker.check("the target", "the submission")


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
