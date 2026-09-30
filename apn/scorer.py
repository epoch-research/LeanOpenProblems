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

from apn.checker import Claim, ProofChecker
from apn.filetree import build_tree_from_tar, read_submission_tar
from apn.workspace import CLAIM_STORE_KEY, Workspace, current_workspace

__all__ = ["CLAIM_STORE_KEY", "proof_scorer", "score_workspace"]

logger = logging.getLogger(__name__)


@scorer(metrics=[accuracy(), stderr()])
def proof_scorer(checker: ProofChecker) -> Scorer:
    """Score a sample by checking the agent's ``Submission/`` module tree (entry
    module ``Spec.lean``) with the configured proof checker (Comparator in
    production)."""

    async def score(state: TaskState, target: Target) -> Score:
        return await score_workspace(state, checker, current_workspace())

    return score


async def score_workspace(
    state: TaskState,
    checker: ProofChecker,
    workspace: Workspace,
    tree_key: str = "submission_contents",
) -> Score:
    # Per-attempt attempt index, kept in the sample store (the react/deepagent
    # attempt_count is not reachable from here). Increments even when
    # max_attempts=1, so a single-attempt sample still tags attempt-1.
    attempt = store().get("_score_call_idx", 0) + 1
    store().set("_score_call_idx", attempt)

    try:
        tar = await read_submission_tar(sandbox(workspace.sandbox))
    except OutputLimitExceededError as exc:
        return Score(
            value=INCORRECT,
            explanation=str(exc),
            metadata={"stage": "submission_oversize", "verifier_output": None},
        )

    _write_submission_sidecar(state, attempt, tar)
    _record_submission_tree(state, tar, tree_key)

    # The claim the agent declared on its submit call. A sample scored
    # without one (e.g. it hit its limits before ever submitting) defaults
    # to "proof" -- deterministic, and such submissions reject anyway.
    claim: Claim = store().get(workspace.claim_key, "proof")
    # The target theorem's fully qualified name (== the sample id except
    # where the manifest overrides it; see apn.dataset.build_dataset).
    decl = state.metadata["decl_name"]

    spec = state.metadata["sketch"]
    async with workspace.check_lock:
        outcome = await checker.check(spec, tar, decl=decl, claim=claim)
    return Score(
        value=CORRECT if outcome.ok else INCORRECT,
        explanation=outcome.detail,
        metadata={
            "stage": outcome.stage,
            "claim": claim,
            "verifier_output": outcome.detail,
        },
    )


def _record_submission_tree(state: TaskState, tar: bytes, key: str) -> None:
    """Set the agent's ``Submission/`` directory as a display tree on sample metadata."""
    try:
        state.metadata[key] = build_tree_from_tar(tar)
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
