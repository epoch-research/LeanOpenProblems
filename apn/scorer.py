"""Scoring: a sample is correct iff the agent produced a complete proof.

The scorer independently re-validates the agent's final sketch with SafeVerify
rather than trusting the solver's own verdict: the proof is correct only if it
compiles, is ``sorry``-free, leaves the target theorem statement intact, and
introduces no disallowed axioms.
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

from apn.safeverify import DEFAULT_ALLOWED_AXIOMS, safe_verify
from apn.sketch import ProofSketch
from apn.verifier.base import LeanVerifier


@scorer(metrics=[accuracy(), stderr()])
def proof_scorer(
    verifier: LeanVerifier,
    allowed_axioms: frozenset[str] = DEFAULT_ALLOWED_AXIOMS,
) -> Scorer:
    """Score a completed sample by re-validating its final sketch."""

    async def score(state: TaskState, target: Target) -> Score:
        final = state.store.get("final_sketch")
        if not isinstance(final, str) or not final:
            return Score(
                value=INCORRECT,
                explanation="The agent did not produce a final sketch.",
            )

        original_text = state.metadata.get("sketch") or state.input_text
        original = ProofSketch(original_text)
        target_declarations = list(state.metadata.get("target_declarations", []))

        verdict = await safe_verify(
            verifier,
            original,
            ProofSketch(final),
            target_declarations,
            allowed_axioms=allowed_axioms,
        )
        return Score(
            value=CORRECT if verdict.is_complete_proof else INCORRECT,
            answer=final,
            explanation=verdict.feedback,
            metadata={
                "compiles": verdict.compiles,
                "statement_preserved": verdict.statement_preserved,
                "has_sorry": verdict.has_sorry,
                "uses_sorry_ax": verdict.uses_sorry_ax,
                "disallowed_axioms": list(verdict.disallowed_axioms),
            },
        )

    return score
