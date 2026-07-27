"""Tests for the gated-submit feedback policy.

When a gated submission is rejected, the agent is told only that verification
failed -- never *why* -- so it cannot probe SafeVerify for gaps. The one
exception: a submission that was too expensive to process -- it ran out of
memory, timed out, or was too large, at either the compile or the safe_verify
step -- gets a slightly more informative (but still amount-free, stage-free)
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


async def test_safeverify_oom_gets_resource_message() -> None:
    assert await _msg("safeverify_resource") == RESOURCE_INCORRECT_MESSAGE


async def test_safeverify_timeout_gets_resource_message() -> None:
    # Same message as OOM: the agent is told it hit a resource limit without
    # learning which, at which stage, the amount, or any other detail.
    assert await _msg("safeverify_timeout") == RESOURCE_INCORRECT_MESSAGE


async def test_compile_submission_oom_gets_resource_message() -> None:
    # An OOM compiling the *submission* is also the agent's expensive proof, not
    # a plain rejection -- so it gets the resource message too (regression guard:
    # this stage was previously omitted from the resource set, silently downgrading
    # it to the opaque message).
    assert await _msg("compile_submission_resource") == RESOURCE_INCORRECT_MESSAGE


async def test_compile_submission_timeout_gets_resource_message() -> None:
    # A timeout compiling the submission -- same family as the safe_verify
    # timeout, same message. (Previously fell through to the opaque message.)
    assert await _msg("compile_submission_timeout") == RESOURCE_INCORRECT_MESSAGE


async def test_compile_submission_oversize_gets_resource_message() -> None:
    # A compiled olean too large to read back is "too expensive to process" too.
    assert await _msg("compile_submission_oversize") == RESOURCE_INCORRECT_MESSAGE


async def test_submission_oversize_gets_resource_message() -> None:
    # The scorer's verdict when the agent's Submission/ is too large to read.
    assert await _msg("submission_oversize") == RESOURCE_INCORRECT_MESSAGE


async def test_plain_safeverify_rejection_stays_opaque() -> None:
    assert await _msg("safeverify") == INCORRECT_MESSAGE


async def test_compile_submission_rejection_stays_opaque() -> None:
    # A plain compile error means the proof was *wrong*, not too expensive.
    assert await _msg("compile_submission") == INCORRECT_MESSAGE


async def test_safeverify_decode_stays_opaque() -> None:
    # A decode failure is neither an OOM, a timeout, nor an oversize -> opaque.
    assert await _msg("safeverify_decode") == INCORRECT_MESSAGE


async def test_compile_submission_decode_stays_opaque() -> None:
    # Likewise a non-utf8 byte in the submission compile output -> opaque.
    assert await _msg("compile_submission_decode") == INCORRECT_MESSAGE


async def test_no_stage_metadata_stays_opaque() -> None:
    score = Score(value=INCORRECT, answer="proof")
    msg = await gated_incorrect_message(AgentState(messages=[]), [score])
    assert msg == INCORRECT_MESSAGE
