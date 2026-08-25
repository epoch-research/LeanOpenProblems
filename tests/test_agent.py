"""Tests for the gated-submit feedback policy.

When a gated submission is rejected, the agent is told only that verification
failed -- never *why* -- so it cannot probe the verifier for gaps. The one
exception: a submission that was too expensive to process -- it ran out of
memory or timed out inside Comparator, or its Submission/ was too large to read
back -- gets a slightly more informative (but still amount-free, stage-free)
message, so the agent knows to look for a cheaper, smaller proof rather than
guessing blindly.
"""

from __future__ import annotations

from inspect_ai.agent import AgentState
from inspect_ai.scorer import INCORRECT, Score

from apn.solver import (
    INCORRECT_MESSAGE,
    RESOURCE_INCORRECT_MESSAGE,
    gated_incorrect_message,
)


def _score(stage: str) -> Score:
    return Score(value=INCORRECT, answer="proof", metadata={"stage": stage})


async def _msg(stage: str) -> str:
    return await gated_incorrect_message(AgentState(messages=[]), [_score(stage)])


async def test_comparator_oom_gets_resource_message() -> None:
    # An OOM inside Comparator (kernel replay / export of the agent's proof) is
    # the agent's expensive proof, not a plain rejection -> resource message.
    assert await _msg("comparator_resource") == RESOURCE_INCORRECT_MESSAGE


async def test_comparator_timeout_gets_resource_message() -> None:
    # Same message as OOM: the agent is told it hit a resource limit without
    # learning which, at which stage, the amount, or any other detail.
    assert await _msg("comparator_timeout") == RESOURCE_INCORRECT_MESSAGE


async def test_submission_oversize_gets_resource_message() -> None:
    # The scorer's verdict when the agent's Submission/ is too large to read.
    assert await _msg("submission_oversize") == RESOURCE_INCORRECT_MESSAGE


async def test_plain_comparator_rejection_stays_opaque() -> None:
    # A plain reject (wrong proof / illegal axiom / statement mismatch / decode
    # error, all mapped to the "comparator" stage) means the proof was *wrong*
    # or malformed, not too expensive -> opaque.
    assert await _msg("comparator") == INCORRECT_MESSAGE


async def test_entry_missing_stays_opaque() -> None:
    # A submission with no well-formed Spec.lean is an ordinary rejection.
    assert await _msg("entry_missing") == INCORRECT_MESSAGE


async def test_no_stage_metadata_stays_opaque() -> None:
    score = Score(value=INCORRECT, answer="proof")
    msg = await gated_incorrect_message(AgentState(messages=[]), [score])
    assert msg == INCORRECT_MESSAGE
