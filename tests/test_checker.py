"""Tests for the proof scorer wiring (with a stub SafeVerify checker).

The real checker (``SandboxSafeVerify``) runs the Lean ``safe_verify`` exe in the
sandbox and is validated against the real toolchain. Here we use a stub checker
and a fake sandbox to verify the scorer reads the agent's proof file and maps a
checker outcome to CORRECT/INCORRECT.
"""

from __future__ import annotations

import pytest
from inspect_ai.model import ModelName
from inspect_ai.scorer import CORRECT, INCORRECT, Score, Target
from inspect_ai.solver import TaskState

import apn.scorer as scorer_mod
from apn.checker import CheckOutcome, SafeVerifyChecker
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
