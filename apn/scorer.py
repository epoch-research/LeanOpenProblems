"""Scoring: a sample is correct iff the agent produced a complete proof.

Validation is delegated to a :class:`~apn.checker.SafeVerifyChecker` -- normally
the kernel-level ``safe_verify`` executable run in the sandbox, which confirms
the submission compiles, implements the target theorem with the same kernel
type, leaves it ``sorry``-free, and uses only the standard axioms.

The submission is the agent's ``Submission/Spec.lean``, read **live** from the
agent's sandbox (not from any solver-written store), so this scorer gives the
same verdict whether Inspect runs it at the end of a sample or mid-loop on each
gated submission (the ``attempts`` mechanism -- see :func:`apn.agent.lean_prover`).

Per attempt this scorer tars ``Submission/`` from the live agent sandbox once,
then uses those bytes three ways: writes an attempt-indexed ``attempt-N.tar``
sidecar next to the eval log for audit; records a nested display tree on the
*sample* metadata (``submission_contents``) for the log viewer and
``scripts/extract_plaintext``; and hands the raw tar to the checker, which
unpacks and builds it in its own sandbox.

The display tree is recorded here, not in the solver, on purpose. The scorer
always runs after the agent -- including when a token/time limit terminates it
(the common exit for open problems, which run until the limit) -- whereas code
placed after the solver's ``run(agent, ...)`` is skipped when a limit raises out
of it, so a solver-side capture is empty on almost every real sample. It goes on
*sample* metadata rather than ``Score.metadata`` to stay out of the event log:
``Score.metadata`` is written per ScoreEvent (so a tree there is copied once per
gated attempt), while ``state.metadata`` writes are not individually
event-logged -- only a solver's net state diff is (via ``SolverTranscript``, and
scoring is not wrapped in one) -- so re-setting it each attempt costs nothing and
only the final value reaches ``EvalSample.metadata``. The verdict's
``stage``/report still go on ``Score.metadata`` (small, per-attempt).

The tar is produced by ``tar`` in the agent's own sandbox (agent-owned as root),
so its bytes are untrusted -- but the checker unpacks and compiles it in a
throwaway, untrusted ``compile`` sandbox, never the trusted scorer (see
:mod:`apn.checker`). So compile-time code execution is contained there, where no
trusted ``target.olean`` or ``safe_verify`` binary exists and there is no path to
the scorer. The remaining attack surface is a memory-safety bug in
``safe_verify``'s deserialization of the agent-influenced olean -- a far higher
bar; see the checker module docstring.
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

        # Tar the agent's Submission/ directory from its (default) workspace
        # sandbox. A read failure is a real sandbox problem -- let it propagate
        # (error the sample) rather than masking it as a rejection.
        tar = await read_submission_tar(sandbox())

        # Record exactly what was scored, two display ways from the one tar
        # already read (both best-effort -- neither may fail scoring):
        #   * an audit sidecar of the raw tar, next to the eval log;
        #   * a nested display tree on the *sample* metadata for the Inspect log
        #     viewer and scripts/extract_plaintext.
        # This capture lives in the scorer, not the solver, for two reasons.
        # (1) Reliability: the scorer always runs after the agent -- including
        # when a token/time limit terminates it (the common exit for open
        # problems) -- whereas any code after the solver's `run(agent, ...)` is
        # skipped when a limit raises out of it. (2) It reuses this one tar read.
        # Putting the tree on sample metadata (not Score.metadata) is what keeps
        # the event log small: Score.metadata is written per ScoreEvent, so a
        # tree there would be copied once per gated attempt; state.metadata
        # writes are not individually event-logged (only a solver's net diff is,
        # via SolverTranscript, and scoring isn't wrapped in one), so re-setting
        # it each gated attempt adds nothing -- only the final value reaches
        # EvalSample.metadata.
        _write_submission_sidecar(state, attempt, tar)
        _record_submission_tree(state, tar)

        # Hand the raw tar to the checker, which unpacks it in its own sandbox
        # and builds (no Python decode on the verification path). The target is
        # the trusted spec the conjecture was posed as -- metadata["sketch"], the
        # single source set by the dataset -- never the agent's Spec.lean, which
        # it may have weakened; safe_verify matches the submission against this
        # target.
        target_spec = state.metadata["sketch"]
        outcome = await checker.check(target_spec, tar)
        return Score(
            value=CORRECT if outcome.ok else INCORRECT,
            # No answer: it is purely cosmetic, and the agent's submission is
            # already recorded in full as the nested display tree on sample
            # metadata (set by _record_submission_tree above).
            explanation=outcome.detail,
            # stage drives the gated-submit message (see apn.agent); report is
            # safe_verify's per-declaration --save JSON (None when it didn't run
            # or wrote nothing) for offline analysis of how each proof/disproof
            # was judged.
            metadata={"stage": outcome.stage, "safeverify_report": outcome.report},
        )

    return score


def _record_submission_tree(state: TaskState, tar: bytes) -> None:
    """Set the agent's ``Submission/`` directory as a display tree on sample metadata.

    Builds a nested :data:`~apn.filetree.FileTreeForLogViewer` from the scored
    tar and stores it on ``state.metadata["submission_contents"]`` for the Inspect
    log viewer and ``scripts/extract_plaintext``.
    """
    try:
        state.metadata["submission_contents"] = build_tree_from_tar(tar)
    except Exception:
        logger.warning(
            "Failed to build the Submission/ display tree from the scored tar; "
            "recording an empty tree (scoring is unaffected)",
            exc_info=True,
        )


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
        # Zero-pad the attempt index (PortBench's sidecar convention) so the
        # files sort lexicographically in attempt order.
        with (sidecar_dir / f"attempt-{attempt:05d}.tar").open("wb") as f:
            f.write(tar)
    except Exception:
        logger.warning("Failed to write submission sidecar", exc_info=True)
