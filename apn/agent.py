"""The Lean-proving solver: a thin wrapper around Inspect's ``deepagent``.

The agent is given the proof file in the sandbox plus tools -- the built-in
``text_editor`` to edit it and ``bash`` for everything else (PyPantograph is
installed in the agent image, so the agent compiles Lean by driving
``pantograph.Server`` from Python; numeric exploration goes through the same
shell) -- and left to prove the theorem. ``deepagent`` runs its own loop and
submits when done.

Submissions can be *gated*: with ``max_attempts`` > 1, Inspect's native
``attempts`` mechanism re-runs the task scorer (SafeVerify) on each submission
and, if it isn't accepted, tells the model to keep going -- up to ``max_attempts``
or until a token/time limit. The model is told only that it was incorrect (the
``incorrect_message`` below), not why, so it cannot probe the verifier for gaps
-- with one exception: if the submission made SafeVerify run out of memory or
time, it is told that much (but not which, nor any amount), so it can aim for a
cheaper proof instead of guessing blindly.
"""

from __future__ import annotations

from inspect_ai.agent import (
    AgentAttempts,
    AgentState,
    AgentSubmit,
    deepagent,
    run,
)
from inspect_ai.model import CompactionSummary, get_model
from inspect_ai.scorer import Score
from inspect_ai.solver import Generate, Solver, TaskState, solver
from inspect_ai.tool import Tool, ToolResult, text_editor, tool
from inspect_ai.util import sandbox

from apn.dataset import strip_license_header
from apn.prompts import user_prompt
from apn.tools import arxiv_search, arxiv_source, bash

# Path of the proof file inside the sample's sandbox.
PROOF_PATH = "/tmp/apn_proof.lean"

# Played back to the model when a gated submission fails verification. Note it
# deliberately reveals nothing about *why* (no SafeVerify output), so the model
# cannot search for verifier gaps.
INCORRECT_MESSAGE = (
    "Your submission did not pass verification. Keep working to find a correct, "
    "complete proof."
)

# The one exception to the opaque policy: when the submission made SafeVerify
# run out of memory or time (rather than being rejected on the merits), tell the
# model that much -- but nothing more. It learns to look for a cheaper proof
# without learning which limit it hit, the amount, or any other detail it could
# turn into a probe. OOM and timeout deliberately share this one wording so the
# model cannot even tell which of the two occurred.
RESOURCE_INCORRECT_MESSAGE = (
    "Your submission did not pass verification: checking it ran out of memory or "
    "timed out. Keep working to find a correct, complete proof that is also "
    "cheaper to check."
)

# SafeVerify stages (see apn.checker) that mean the agent's proof was too
# expensive to *verify*, as opposed to wrong. Only these get the more
# informative message; every other rejection stays opaque.
_RESOURCE_STAGES = frozenset({"safeverify_resource", "safeverify_timeout"})


async def gated_incorrect_message(state: AgentState, scores: list[Score]) -> str:
    """Pick the reply for a rejected gated submission.

    Opaque by default; the resource message only when a score's ``stage`` marks
    a SafeVerify OOM/timeout (``state`` is unused -- the verdict is all we need).
    """
    if any((s.metadata or {}).get("stage") in _RESOURCE_STAGES for s in scores):
        return RESOURCE_INCORRECT_MESSAGE
    return INCORRECT_MESSAGE


@tool
def submit() -> Tool:
    """A no-argument submit tool.

    The proof is the edited file, not a text answer, so submitting takes no
    arguments -- the model just signals it is done.
    """

    async def execute() -> ToolResult:
        """Submit the proof for verification.

        Call this once the file compiles with no remaining `sorry`. Takes no
        arguments: your edited file is the submission.
        """
        return "Submitted."

    return execute


@solver
def lean_prover(
    model: str | None = None,
    max_attempts: int = 1,
    literature: bool = False,
) -> Solver:
    """Prove the sample's theorem with a ``deepagent``.

    Writes the initial Lean file (from ``metadata['sketch']``, else the sample
    input) into the sandbox and runs the agent. The proof is the edited file in
    the sandbox; the scorer reads it back from there (see :mod:`apn.scorer`), so
    the solver keeps no state of its own.

    Args:
        model: Optional model override for the agent.
        max_attempts: With ``> 1``, enables *gated submit* via Inspect's native
            ``attempts``: each submission is re-scored by the task scorer
            (SafeVerify) and, if not accepted, the model is told to keep going
            (up to this many attempts, or until a token/time limit). With ``1``
            (default), the first submission ends the loop and is validated only
            by the final scorer.
        literature: If true, give the agent ``arxiv_search`` / ``arxiv_source``
            (the network call runs host-side; the sandbox stays airgapped). Both
            are gated to papers predating the benchmark paper, but they still
            change the run condition (literature-augmented vs. closed-book), so
            this is off by default.
    """

    async def solve(state: TaskState, generate: Generate) -> TaskState:
        # Strip the copyright/license banner before the agent ever sees the file:
        # it is identical boilerplate across every conjecture and pure token
        # waste in the agent's context. The scorer still compiles the original
        # sketch as its target, so verification is unaffected (comments don't
        # reach the olean anyway).
        sketch = strip_license_header(state.metadata.get("sketch") or state.input_text)
        await sandbox().write_file(PROOF_PATH, sketch)

        tools = [
            text_editor(),
            # Shell access to the workspace image: the agent drives PyPantograph
            # from python3 to compile the proof file, and the same shell is its
            # numeric scratchpad (sympy/numpy are baked in).
            bash(timeout=300),
        ]
        if literature:
            # Literature access, gated to papers predating the benchmark paper so
            # they can't surface a later solution to these still-open conjectures.
            tools += [arxiv_search(), arxiv_source()]

        agent = deepagent(
            tools=tools,
            memory=False,
            # Gating: re-score each submission with the task scorer (SafeVerify);
            # on failure the model is told only that it failed (no verifier
            # output) and keeps going. gated_incorrect_message keeps that opaque
            # except for a SafeVerify OOM/timeout, where it adds an amount-free
            # "ran out of memory or timed out". max_attempts=1 disables this.
            attempts=AgentAttempts(
                attempts=max_attempts, incorrect_message=gated_incorrect_message
            ),
            # Name it distinctly from the subagents' "submit" tool and keep the
            # call in the message history. keep_in_messages=True stops react from
            # folding the tool's return into the assistant message; the distinct
            # name means the main loop's submission scan can never match a
            # subagent's "submit" (no early-termination collision).
            submit=AgentSubmit(
                tool=submit(), name="submit_proof", keep_in_messages=True
            ),
            # The default continue message is very generic ("proceed to the next step"), this one
            # might be better at avoiding doom loops.
            on_continue="Continue working on the problem.",
            compaction=CompactionSummary(threshold=300_000),
            model=get_model(model) if model is not None else None,
        )
        await run(agent, user_prompt(PROOF_PATH, state.token_limit, literature))
        state.completed = True
        return state

    return solve
