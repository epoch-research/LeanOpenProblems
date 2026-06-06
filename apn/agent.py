"""The Lean-proving solver: a thin wrapper around an Inspect agent.

The agent is given the proof file in the sandbox plus tools -- the built-in
``text_editor`` to edit it and ``bash`` for everything else (PyPantograph is
installed in the agent image, so the agent compiles Lean by driving
``pantograph.Server`` from Python; numeric exploration goes through the same
shell) -- and left to prove the theorem. The agent runs its own loop and
submits when done.

Two agent loops are supported, selected by ``agent_type``: Inspect's
``deepagent`` (the default -- subagents, planning, an opinionated system prompt)
and its plain ``react`` agent (a bare tool-use loop). The solver only ever
configures functionality common to both -- tools, the gated ``attempts``
mechanism, the no-argument ``submit`` tool, the continue message, compaction,
and the model -- so swapping the loop changes nothing else about the run. See
:func:`build_agent`.

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

from typing import Callable, Literal, Sequence

from inspect_ai.agent import (
    Agent,
    AgentAttempts,
    AgentState,
    AgentSubmit,
    deepagent,
    react,
    run,
)
from inspect_ai.model import CompactionStrategy, CompactionSummary, Model, get_model
from inspect_ai.scorer import Score
from inspect_ai.solver import Generate, Solver, TaskState, solver
from inspect_ai.tool import Tool, ToolDef, ToolResult, ToolSource, text_editor, tool
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


# The agent loops we can run. "deep" is Inspect's batteries-included
# ``deepagent`` (subagents, planning, opinionated prompt); "react" is its plain
# tool-use loop. Both are configured identically by build_agent. The default is
# chosen once, at the task level (see :func:`apn.task.apn_oeis`).
AgentType = Literal["deep", "react"]


def build_agent(
    agent_type: AgentType,
    *,
    tools: Sequence[Tool | ToolDef | ToolSource],
    attempts: AgentAttempts,
    submit: AgentSubmit,
    on_continue: str,
    compaction: CompactionStrategy,
    model: Model | None,
) -> Agent:
    """Construct the configured agent loop.

    Only exposes functionality common to ``deepagent`` and ``react`` so the two
    behave identically apart from the loop itself: the same tools, the gated
    ``attempts`` mechanism, the no-argument ``submit`` tool, the continue
    message, compaction, and the model. Everything specific to one agent stays
    at its default.
    """
    constructor: Callable[..., Agent]
    if agent_type == "deep":
        constructor = deepagent
    elif agent_type == "react":
        constructor = react
    else:
        raise ValueError(f"Unknown agent_type {agent_type!r}; expected 'deep' or 'react'.")
    # deepagent layers extras (memory, subagents, todo_write) on top of react;
    # we leave all of them at their defaults so the two loops differ only in the
    # loop itself.
    return constructor(
        tools=tools,
        attempts=attempts,
        submit=submit,
        on_continue=on_continue,
        compaction=compaction,
        model=model,
    )


@solver
def lean_prover(
    agent_type: AgentType,
    model: str | None = None,
    max_attempts: int = 1,
    literature: bool = False,
) -> Solver:
    """Prove the sample's theorem with an Inspect agent.

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
        agent_type: Which agent loop to run -- ``"deep"`` for Inspect's
            ``deepagent`` or ``"react"`` for its plain react agent. Both get the
            same tools, gating, submit tool, and prompt; see :func:`build_agent`.
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

        agent = build_agent(
            agent_type,
            tools=tools,
            # Gating: re-score each submission with the task scorer (SafeVerify);
            # on failure the model is told only that it failed (no verifier
            # output) and keeps going. gated_incorrect_message keeps that opaque
            # except for a SafeVerify OOM/timeout, where it adds an amount-free
            # "ran out of memory or timed out". max_attempts=1 disables this.
            attempts=AgentAttempts(
                attempts=max_attempts, incorrect_message=gated_incorrect_message
            ),
            # Name it distinctly from any subagents' "submit" tool and keep the
            # call in the message history. keep_in_messages=True stops the loop
            # from folding the tool's return into the assistant message; the
            # distinct name means the main loop's submission scan can never match
            # a subagent's "submit" (no early-termination collision).
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
