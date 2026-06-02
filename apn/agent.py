"""The Lean-proving solver: a thin wrapper around Inspect's ``deepagent``.

The agent is given the proof file in the sandbox plus tools -- the built-in
``text_editor`` to edit it, ``lean_check`` to compile it, and ``bash`` (python)
to explore -- and left to prove the theorem. ``deepagent`` runs its own loop and
submits when done.

Submissions can be *gated*: with ``max_attempts`` > 1, Inspect's native
``attempts`` mechanism re-runs the task scorer (SafeVerify) on each submission
and, if it isn't accepted, tells the model to keep going -- up to ``max_attempts``
or until a token/time limit. The model is told only that it was incorrect (the
``incorrect_message`` below), not why, so it cannot probe the verifier for gaps.
"""

from __future__ import annotations

from inspect_ai.agent import AgentAttempts, AgentSubmit, deepagent, run
from inspect_ai.model import CompactionSummary, get_model
from inspect_ai.solver import Generate, Solver, TaskState, solver
from inspect_ai.tool import Tool, ToolResult, bash, text_editor, tool
from inspect_ai.util import sandbox

from apn.prompts import LEAN_INSTRUCTIONS, LITERATURE_INSTRUCTIONS, render_task
from apn.tools import arxiv_search, arxiv_source, lean_check
from apn.verifier.base import LeanVerifier

# Path of the proof file inside the sample's sandbox.
PROOF_PATH = "/tmp/apn_proof.lean"

# Played back to the model when a gated submission fails verification. Note it
# deliberately reveals nothing about *why* (no SafeVerify output), so the model
# cannot search for verifier gaps.
INCORRECT_MESSAGE = (
    "Your submission did not pass verification. Keep working to find a correct, "
    "complete proof."
)


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
    verifier: LeanVerifier,
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
        verifier: In-loop compiler for the ``lean_check`` tool.
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
        sketch = state.metadata.get("sketch") or state.input_text
        await sandbox().write_file(PROOF_PATH, sketch)

        tools = [
            text_editor(),
            lean_check(verifier, PROOF_PATH),
            # Shell access to the workspace image, so the agent can run `python3`
            # to explore numerically (compute sequence terms, check small cases)
            # before committing to a Lean proof.
            bash(timeout=120),
        ]
        instructions = LEAN_INSTRUCTIONS
        if literature:
            # Literature access, gated to papers predating the benchmark paper so
            # they can't surface a later solution to these still-open conjectures.
            tools += [arxiv_search(), arxiv_source()]
            instructions += LITERATURE_INSTRUCTIONS

        agent = deepagent(
            tools=tools,
            instructions=instructions,
            memory=False,
            # Gating: re-score each submission with the task scorer (SafeVerify);
            # on failure the model is told only INCORRECT_MESSAGE (no verifier
            # output) and keeps going. max_attempts=1 disables this.
            attempts=AgentAttempts(
                attempts=max_attempts, incorrect_message=INCORRECT_MESSAGE
            ),
            # Name it distinctly from the subagents' "submit" tool and keep the
            # call in the message history. keep_in_messages=True stops react from
            # folding the tool's return into the assistant message; the distinct
            # name means the main loop's submission scan can never match a
            # subagent's "submit" (no early-termination collision).
            submit=AgentSubmit(
                tool=submit(), name="submit_proof", keep_in_messages=True
            ),
            on_continue="Continue working on the problem.",
            compaction=CompactionSummary(threshold=300_000),
            model=get_model(model) if model is not None else None,
        )
        await run(agent, render_task(PROOF_PATH))
        state.completed = True
        return state

    return solve
