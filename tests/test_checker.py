"""Tests for the proof scorer wiring (with a stub SafeVerify checker).

The real checker (``SandboxSafeVerify``) runs the Lean ``safe_verify`` exe in the
sandbox and is validated against the real toolchain. Here we use a stub checker
to verify the scorer maps a checker outcome to CORRECT/INCORRECT and handles a
missing proof.
"""

from __future__ import annotations

from inspect_ai.model import ModelName
from inspect_ai.scorer import CORRECT, INCORRECT, Score, Target
from inspect_ai.solver import TaskState

from apn.checker import CheckOutcome, SafeVerifyChecker
from apn.scorer import proof_scorer

SKETCH = "import Mathlib\ntheorem tgt : True := by sorry\n"


class StubChecker:
    def __init__(self, ok: bool) -> None:
        self._ok = ok

    async def check(self, target: str, submission: str) -> CheckOutcome:
        return CheckOutcome(ok=self._ok, stage="stub", detail="stub outcome")


def _state(final_proof: str | None) -> TaskState:
    state = TaskState(
        model=ModelName("mockllm/model"),
        sample_id="t",
        epoch=1,
        input=SKETCH,
        messages=[],
        metadata={"sketch": SKETCH, "target_declarations": ["tgt"]},
    )
    if final_proof is not None:
        state.store.set("final_proof", final_proof)
    return state


async def _score(checker: SafeVerifyChecker, final_proof: str | None) -> Score:
    result = await proof_scorer(checker)(_state(final_proof), Target(""))
    assert result is not None
    return result


async def test_scorer_correct_when_checker_accepts() -> None:
    score = await _score(StubChecker(True), "proof")
    assert score.value == CORRECT
    assert score.answer == "proof"


async def test_scorer_incorrect_when_checker_rejects() -> None:
    score = await _score(StubChecker(False), "proof")
    assert score.value == INCORRECT


async def test_scorer_incorrect_when_no_proof() -> None:
    score = await _score(StubChecker(True), None)
    assert score.value == INCORRECT
