from __future__ import annotations

import logging
from typing import Any

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
SWARM_LEDGER_KEY = "inspect_swarm:ledger"


def _member_key(key: str) -> str:
    member = current_member()
    return key if member is None else f"{key}:{member}"


def claim_store_key() -> str:
    return _member_key(CLAIM_STORE_KEY)


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
        # Known limitation: in a swarm, every member writes this same key, so the last one wins.
        return await _score_sandbox(state, checker, sandbox(), "submission_contents")

    return score


async def _score_swarm(state: TaskState, checker: ProofChecker) -> Score:
    record = state.store.get(SWARM_RESULT_KEY)
    scores: dict[str, Score] = {}
    rows: list[list[str]] = []
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
        score = scores[name]
        assert score.metadata is not None and score.explanation is not None
        claim = (
            'did not call `submit_proof()`, defaulted to `claim="proof"`'
            if recorded is None
            else f'called `submit_proof(claim="{recorded}")`'
        )
        check = next(
            (line for line in reversed(score.explanation.splitlines()) if line.strip()),
            "",
        )
        result = "CORRECT" if score.value == CORRECT else "INCORRECT"
        rows.append([name, m["status"], result, claim, score.metadata["stage"], check])
    passed = [name for name, s in scores.items() if s.value == CORRECT]
    return Score(
        value=CORRECT if passed else INCORRECT,
        explanation=_swarm_explanation(
            len(scores), passed, state.store.get(SWARM_LEDGER_KEY), rows
        ),
        metadata={
            "passed": passed,
            "members": {name: s.metadata for name, s in scores.items()},
        },
    )


def _swarm_explanation(
    size: int, passed: list[str], ledger: dict[str, Any], rows: list[list[str]]
) -> str:
    if passed:
        summary = (
            f"Swarm of {size}: {len(passed)} members' work passes "
            f"({', '.join(passed)})."
        )
    else:
        summary = f"Swarm of {size}: no member's work passes."
    summary += f" Stop reason: {ledger['stop_reason']}."
    if ledger["ended_by"] is not None:
        summary += f" Ended by: {ledger['ended_by']}."
    table = [
        "| Member | Status | Result | Claim | Stage | Checker |",
        "| --- | --- | --- | --- | --- | --- |",
        *(
            "| " + " | ".join(cell.replace("|", "\\|") for cell in row) + " |"
            for row in rows
        ),
    ]
    return "\n".join([summary, "", *table])


async def _score_sandbox(
    state: TaskState,
    checker: ProofChecker,
    sb: SandboxEnvironment,
    tree_key: str,
) -> Score:
    # Per-attempt attempt index, kept in the sample store (the react/deepagent
    # attempt_count is not reachable from here). Increments even when
    # max_attempts=1, so a single-attempt sample still tags attempt-1.
    attempt_key = _member_key("_score_call_idx")
    attempt = store().get(attempt_key, 0) + 1
    store().set(attempt_key, attempt)

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
    """Write the scored ``Submission/`` tar to ``artifacts/<uuid>/attempt-N.tar``,
    or ``artifacts/<uuid>/<member>/attempt-N.tar`` for a swarm member."""
    try:
        # private Inspect API -- no public way to get the log path from a scorer.
        from inspect_ai.log._samples import sample_active
        from upath import UPath

        active = sample_active()
        if active is None:
            logger.warning("Could not get active sample; skipping submission sidecar")
            return
        sidecar_dir = UPath(active.log_location).parent / "artifacts" / state.uuid
        member = current_member()
        if member is not None:
            sidecar_dir = sidecar_dir / member
        sidecar_dir.mkdir(parents=True, exist_ok=True)
        # Zero-pad the attempt index (PortBench's sidecar convention) so the
        # files sort lexicographically in attempt order.
        with (sidecar_dir / f"attempt-{attempt:05d}.tar").open("wb") as f:
            f.write(tar)
    except Exception:
        logger.warning("Failed to write submission sidecar", exc_info=True)
