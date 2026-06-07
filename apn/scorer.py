"""Scoring: a sample is correct iff the agent produced a complete proof.

Validation is delegated to a :class:`~apn.checker.SafeVerifyChecker` -- normally
the kernel-level ``safe_verify`` executable run in the sandbox, which confirms
the submission compiles, implements the target theorem with the same kernel
type, leaves it ``sorry``-free, and uses only the standard axioms.

The submission is the agent's ``Submission/`` subtree, read **live** from the
agent's sandbox (not from any solver-written store), so this scorer gives the
same verdict whether Inspect runs it at the end of a sample or mid-loop on each
gated submission (the ``attempts`` mechanism -- see :func:`apn.agent.lean_prover`).

Per attempt this scorer: tars ``Submission/`` from the live agent sandbox;
writes an attempt-indexed ``attempt-N.tar`` sidecar next to the eval log for
audit; and hands the raw tar to the checker, which unpacks and builds it in its
own sandbox. The verdict's ``stage``/report go on ``Score.metadata``; the full
tree never does (it would bloat the event log over up to ``max_attempts``
attempts). The solver sets the nested display tree once per sample instead (see
:mod:`apn.agent`).

Known, accepted security hole (out of scope, like the pre-existing root-code-exec
hole in :mod:`apn.checker`): the tar is produced by ``tar`` running in the
agent's own sandbox, which the agent owns as root, so its bytes are untrusted.
A forged regular-file member with a traversal name (e.g. ``../_apn_score/
target.olean``) would, when staged under ``SUBMISSION_DIR`` in the scorer
sandbox, escape and could clobber a trusted artifact before verification -- a
Zip-Slip. We do **not** guard against it here: it requires the agent to tamper
with its own ``tar`` (a real but unlikely capability), and the deeper issue --
that compiling any submission already runs arbitrary code as root in the scorer
sandbox -- subsumes it. Both are tracked as a single separate hardening effort
(non-root build, hash-pinned target), not patched piecemeal.
"""

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
from inspect_ai.util import sandbox, store

from apn.checker import SafeVerifyChecker
from apn.filetree import read_submission_tar

logger = logging.getLogger(__name__)


@scorer(metrics=[accuracy(), stderr()])
def proof_scorer(checker: SafeVerifyChecker) -> Scorer:
    """Score a sample by checking the agent's ``Submission/`` subtree with SafeVerify."""

    async def score(state: TaskState, target: Target) -> Score:
        # Per-attempt attempt index, kept in the sample store (the react/deepagent
        # attempt_count is not reachable from here). Increments even when
        # max_attempts=1, so a single-attempt sample still tags attempt-1.
        attempt = store().get("_score_call_idx", 0) + 1
        store().set("_score_call_idx", attempt)

        # Tar the agent's Submission/ subtree from its (default) workspace
        # sandbox. A read failure is a real sandbox problem -- let it propagate
        # (error the sample) rather than masking it as a rejection.
        tar = await read_submission_tar(sandbox())

        # An audit sidecar of exactly what was scored, next to the eval log.
        # Never fail scoring on a sidecar error.
        _write_submission_sidecar(state, attempt, tar)

        # Hand the raw tar to the checker, which unpacks it in its own sandbox
        # and builds (no Python decode on the verification path). The target is
        # the trusted spec the conjecture was posed as (metadata["sketch"], else
        # the sample input) -- never the agent's Spec.lean, which it may have
        # weakened; safe_verify matches the submission against this target.
        target_spec = state.metadata.get("sketch") or state.input_text
        outcome = await checker.check(target_spec, tar)
        return Score(
            value=CORRECT if outcome.ok else INCORRECT,
            # No answer: it is purely cosmetic, and the agent's submission is
            # already recorded in full as the nested display tree on sample
            # metadata (set once by the solver, see apn.agent).
            explanation=outcome.detail,
            # stage drives the gated-submit message (see apn.agent); report is
            # safe_verify's per-declaration --save JSON (None when it didn't run
            # or wrote nothing) for offline analysis of how each proof/disproof
            # was judged.
            metadata={"stage": outcome.stage, "safeverify_report": outcome.report},
        )

    return score


def _write_submission_sidecar(state: TaskState, attempt: int, tar: bytes) -> None:
    """Write the scored ``Submission/`` tar to ``artifacts/<uuid>/attempt-N.tar``.

    Mirrors PortBench's ``_write_agent_code_sidecar``: resolves the log dir via
    the private ``sample_active().log_location``. Best-effort -- any failure is
    logged and swallowed so a sidecar problem never errors a sample.
    """
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
        with (sidecar_dir / f"attempt-{attempt}.tar").open("wb") as f:
            f.write(tar)
    except Exception:
        logger.warning("Failed to write submission sidecar", exc_info=True)
