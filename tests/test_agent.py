"""Tests for the gated-submit feedback policy.

When a gated submission is rejected, the agent is told only that verification
failed -- never *why* -- so it cannot probe SafeVerify for gaps. The one
exception: a submission that made SafeVerify run out of memory or time gets a
slightly more informative (but still amount-free) message, so the agent knows
to look for a cheaper proof rather than guessing blindly.
"""

from __future__ import annotations

from inspect_ai.agent import AgentState
from inspect_ai.scorer import INCORRECT, Score

from apn.agent import (
    INCORRECT_MESSAGE,
    RESOURCE_INCORRECT_MESSAGE,
    gated_incorrect_message,
)


def _score(stage: str) -> Score:
    return Score(value=INCORRECT, answer="proof", metadata={"stage": stage})


async def _msg(stage: str) -> str:
    return await gated_incorrect_message(AgentState(messages=[]), [_score(stage)])


async def test_safeverify_oom_gets_resource_message() -> None:
    assert await _msg("safeverify_resource") == RESOURCE_INCORRECT_MESSAGE


async def test_safeverify_timeout_gets_resource_message() -> None:
    # Same message as OOM: the agent is told "ran out of memory or timed out"
    # without learning which, the amount, or any other detail.
    assert await _msg("safeverify_timeout") == RESOURCE_INCORRECT_MESSAGE


async def test_plain_safeverify_rejection_stays_opaque() -> None:
    assert await _msg("safeverify") == INCORRECT_MESSAGE


async def test_compile_submission_rejection_stays_opaque() -> None:
    assert await _msg("compile_submission") == INCORRECT_MESSAGE


async def test_safeverify_decode_stays_opaque() -> None:
    # A decode failure is neither an OOM nor a timeout -> opaque.
    assert await _msg("safeverify_decode") == INCORRECT_MESSAGE


async def test_no_stage_metadata_stays_opaque() -> None:
    score = Score(value=INCORRECT, answer="proof")
    msg = await gated_incorrect_message(AgentState(messages=[]), [score])
    assert msg == INCORRECT_MESSAGE
