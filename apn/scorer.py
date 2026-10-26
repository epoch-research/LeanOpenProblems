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
from inspect_ai.util import (
    OutputLimitExceededError,
    SandboxEnvironment,
    sandbox,
    store,
    tool_state_scope,
)

from apn.checker import Claim, ProofChecker, current_member
from apn.filetree import build_tree_from_tar, read_submission_tar

logger = logging.getLogger(__name__)

# Where the submit tool records the agent's declared claim (see apn.solver).
CLAIM_STORE_KEY = "submission_claim"

SWARM_RESULT_KEY = "inspect_swarm:result"


def claim_store_key() -> str:
    member = current_member()
    return CLAIM_STORE_KEY if member is None else f"{CLAIM_STORE_KEY}:{member}"


@scorer(metrics=[accuracy(), stderr()])
def proof_scorer(checker: ProofChecker, swarm: bool = False) -> Scorer:
    """Score a sample by checking the agent's ``Submission/`` module tree (entry
    module ``Spec.lean``) with the configured proof checker (Comparator in
    production).

    With ``swarm``, a check inside a member scores that member's own sandbox,
    and the final score after the swarm checks every member's sandbox: CORRECT
    if any member's submission passes."""

    async def score(state: TaskState, target: Target) -> Score:
        if swarm and current_member() is None:
            return await _score_swarm(state, checker)
        return await _score_sandbox(state, checker, sandbox(), "submission_contents")

    return score


async def _score_swarm(state: TaskState, checker: ProofChecker) -> Score:
    record = state.store.get(SWARM_RESULT_KEY)
    scores: dict[str, Score] = {}
    stages: dict[str, str] = {}
    claims: dict[str, str] = {}
    for m in record["members"]:
        name = m["name"]
        with tool_state_scope(name):
            recorded = store().get(claim_store_key())
            scores[name] = await _score_sandbox(
                state,
                checker,
                sandbox(m["sandbox"]),
                f"submission_contents_{name}",
            )
        metadata = scores[name].metadata
        assert metadata is not None
        stages[name] = metadata["stage"]
        claims[name] = (
            'did not call submit_proof(), defaulted to claim="proof"'
            if recorded is None
            else f'called submit_proof(claim="{recorded}")'
        )
    passed = [name for name, s in scores.items() if s.value == CORRECT]
    return Score(
        value=CORRECT if passed else INCORRECT,
        explanation=_swarm_explanation(scores, stages, claims, passed),
        metadata={
            "passed": passed,
            "members": {name: s.metadata for name, s in scores.items()},
        },
    )


def _swarm_explanation(
    scores: dict[str, Score],
    stages: dict[str, str],
    claims: dict[str, str],
    passed: list[str],
) -> str:
    if passed:
        summary = (
            f"Swarm of {len(scores)}: {len(passed)} members' work passes "
            f"({', '.join(passed)})."
        )
    else:
        summary = f"Swarm of {len(scores)}: no member's work passes."
    width = max(len(stage) for stage in stages.values())
    lines = [
        f"{name}: {'CORRECT' if s.value == CORRECT else 'INCORRECT':<9}  "
        f"{stages[name]:<{width}}  {claims[name]}"
        for name, s in scores.items()
    ]
    return "\n".join([summary, *lines])


async def _score_sandbox(
    state: TaskState,
    checker: ProofChecker,
    sb: SandboxEnvironment,
    tree_key: str,
) -> Score:
    # Per-attempt attempt index, kept in the sample store (the react/deepagent
    # attempt_count is not reachable from here). Increments even when
    # max_attempts=1, so a single-attempt sample still tags attempt-1.
    attempt = store().get("_score_call_idx", 0) + 1
    store().set("_score_call_idx", attempt)

    try:
        tar = await read_submission_tar(sb)
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
    recorded: Claim | None = store().get(claim_store_key())
    claim: Claim = "proof" if recorded is None else recorded
    # The target theorem's fully qualified name (== the sample id except
    # where the manifest overrides it; see apn.dataset.build_dataset).
    decl = state.metadata["decl_name"]

    spec = state.metadata["sketch"]
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
