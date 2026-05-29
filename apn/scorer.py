"""Scoring: a sample is correct iff the agent produced a complete proof.

Validation is delegated to a :class:`~apn.checker.SafeVerifyChecker` -- normally
the kernel-level ``safe_verify`` executable run in the sandbox, which confirms
the submission compiles, implements the target theorem with the same kernel
type, leaves it ``sorry``-free, and uses only the standard axioms.
"""

from __future__ import annotations

from inspect_ai.scorer import (
    CORRECT,
    INCORRECT,
    Score,
    Scorer,
    Target,
    accuracy,
    scorer,
    stderr,
)
from inspect_ai.solver import TaskState

from apn.checker import SafeVerifyChecker


@scorer(metrics=[accuracy(), stderr()])
def proof_scorer(checker: SafeVerifyChecker) -> Scorer:
    """Score a completed sample by checking its final proof with SafeVerify."""

    async def score(state: TaskState, target: Target) -> Score:
        final = state.store.get("final_proof")
        if not isinstance(final, str) or not final:
            return Score(
                value=INCORRECT,
                explanation="The agent did not produce a final proof.",
            )

        original = state.metadata.get("sketch") or state.input_text
        outcome = await checker.check(original, final)
        return Score(
            value=CORRECT if outcome.ok else INCORRECT,
            answer=final,
            explanation=outcome.detail,
            metadata={"stage": outcome.stage},
        )

    return score
