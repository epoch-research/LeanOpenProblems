"""Scoring: a sample is correct iff the agent produced a complete proof.

Validation is delegated to a :class:`~apn.checker.SafeVerifyChecker` -- normally
the kernel-level ``safe_verify`` executable run in the sandbox, which confirms
the submission compiles, implements the target theorem with the same kernel
type, leaves it ``sorry``-free, and uses only the standard axioms.

The submission is read **live** from the agent's proof file in the sandbox (not
from any solver-written store), so this scorer gives the same verdict whether
Inspect runs it at the end of a sample or react runs it mid-loop on each
submission (the ``attempts`` gating mechanism -- see :func:`apn.agent.lean_prover`).
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
from inspect_ai.util import sandbox

from apn.agent import PROOF_PATH
from apn.checker import SafeVerifyChecker


@scorer(metrics=[accuracy(), stderr()])
def proof_scorer(checker: SafeVerifyChecker) -> Scorer:
    """Score a sample by checking the agent's proof file with SafeVerify."""

    async def score(state: TaskState, target: Target) -> Score:
        # Read the agent's current proof file from its (default) workspace
        # sandbox. A read failure is a real sandbox problem -- let it propagate
        # (error the sample) rather than masking it as a rejection.
        submission = await sandbox().read_file(PROOF_PATH)
        original = state.metadata.get("sketch") or state.input_text
        outcome = await checker.check(original, submission)
        return Score(
            value=CORRECT if outcome.ok else INCORRECT,
            answer=submission,
            explanation=outcome.detail,
            # stage drives the gated-submit message (see apn.agent); report is
            # safe_verify's per-declaration --save JSON (None when it didn't run
            # or wrote nothing) for offline analysis of how each proof/disproof
            # was judged.
            metadata={"stage": outcome.stage, "safeverify_report": outcome.report},
        )

    return score
