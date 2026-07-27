from __future__ import annotations

import logging

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
from inspect_ai.util import OutputLimitExceededError, sandbox, store

from apn.checker import SafeVerifyChecker
from apn.filetree import build_tree_from_tar, read_submission_tar

logger = logging.getLogger(__name__)


@scorer(metrics=[accuracy(), stderr()])
def proof_scorer(checker: SafeVerifyChecker) -> Scorer:
    """Score a sample by checking the agent's ``Submission/Spec.lean`` with SafeVerify."""

    async def score(state: TaskState, target: Target) -> Score:
        # Per-attempt attempt index, kept in the sample store (the react/deepagent
        # attempt_count is not reachable from here). Increments even when
        # max_attempts=1, so a single-attempt sample still tags attempt-1.
        attempt = store().get("_score_call_idx", 0) + 1
        store().set("_score_call_idx", attempt)

        try:
            tar = await read_submission_tar(sandbox())
        except OutputLimitExceededError as exc:
            return Score(
                value=INCORRECT,
                explanation=str(exc),
                metadata={"stage": "submission_oversize", "safeverify_report": None},
            )

        _write_submission_sidecar(state, attempt, tar)
        _record_submission_tree(state, tar)

        target_spec = state.metadata["sketch"]
        outcome = await checker.check(target_spec, tar)
        return Score(
            value=CORRECT if outcome.ok else INCORRECT,
            explanation=outcome.detail,
            metadata={"stage": outcome.stage, "safeverify_report": outcome.report},
        )

    return score


def _record_submission_tree(state: TaskState, tar: bytes) -> None:
    """Set the agent's ``Submission/`` directory as a display tree on sample metadata."""
    try:
        state.metadata["submission_contents"] = build_tree_from_tar(tar)
    except Exception:
        logger.warning(
            "Failed to build the Submission/ display tree from the scored tar; "
            "recording an empty tree (scoring is unaffected)",
            exc_info=True,
        )


def _write_submission_sidecar(state: TaskState, attempt: int, tar: bytes) -> None:
    """Write the scored ``Submission/`` tar to ``artifacts/<uuid>/attempt-N.tar``."""
    try:
        # private Inspect API -- no public way to get the log path from a scorer.
        from inspect_ai.log._samples import sample_active
        from upath import UPath

        active = sample_active()
        if active is None:
            logger.warning("Could not get active sample; skipping submission sidecar")
            return
        sidecar_dir = UPath(active.log_location).parent / "artifacts" / state.uuid
        sidecar_dir.mkdir(parents=True, exist_ok=True)
        # Zero-pad the attempt index (PortBench's sidecar convention) so the
        # files sort lexicographically in attempt order.
        with (sidecar_dir / f"attempt-{attempt:05d}.tar").open("wb") as f:
            f.write(tar)
    except Exception:
        logger.warning("Failed to write submission sidecar", exc_info=True)
