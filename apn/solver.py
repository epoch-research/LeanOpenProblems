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
-- with one exception: if the submission was too expensive to process (it ran
out of memory, timed out, or was too large to handle, at either the compile or
the safe_verify step), it is told that much (but not which, at which stage, nor
any amount), so it can aim for a cheaper, smaller proof instead of guessing
blindly.
"""

from __future__ import annotations

import logging
from typing import Callable, Literal, Sequence

from inspect_ai.agent import (
    Agent,
    AgentAttempts,
    AgentState,
    AgentSubmit,
    as_solver,
    deepagent,
    react,
)
from inspect_ai.model import (
    ChatMessageUser,
    CompactionStrategy,
    CompactionSummary,
    Model,
    get_model,
)
from inspect_ai.scorer import Score
from inspect_ai.solver import Generate, Solver, TaskState, solver
from inspect_ai.tool import Tool, ToolDef, ToolResult, ToolSource, text_editor, tool
from inspect_ai.util import sandbox

from apn.layout import ENTRY_PATH
from apn.prompts import user_prompt
from apn.tools import bash, resources

logger = logging.getLogger(__name__)

# Played back to the model when a gated submission fails verification. Note it
# deliberately reveals nothing about *why* (no SafeVerify output), so the model
# cannot search for verifier gaps.
INCORRECT_MESSAGE = (
    "Your submission did not pass verification. Keep working to find a correct, "
    "complete proof."
)

# The one exception to the opaque policy: when the submission was too expensive
# to process (rather than rejected on the merits) -- it ran out of memory, timed
# out, or was too large to handle -- tell the model that much, but nothing more.
# It learns to look for a cheaper, smaller proof without learning which limit it
# hit, at which stage, the amount, or any other detail it could turn into a
# probe. All of these failure modes deliberately share this one wording so the
# model cannot even tell which of them occurred.
RESOURCE_INCORRECT_MESSAGE = (
    "Checking your submission exceeded a resource limit (it "
    "ran out of memory, timed out, or created files that were too large). Keep working to find a "
    "correct, complete proof that is cheaper to check."
)

# Stages (see apn.checker / apn.scorer) that mean the agent's proof was too
# expensive to *process* -- OOM, timeout, or too large to read out of the
# sandbox -- as opposed to wrong. These span both agent-side steps: compiling
# the submission AND running safe_verify on it (a death in either is the agent's
# expensive proof, not our infra), plus the scorer's read of an oversized
# Submission/. Only these get the more informative message; every other
# rejection -- a plain compile error, a plain safe_verify rejection, a decode
# failure -- stays opaque. (Keep in sync with the stages apn.checker.check and
# apn.scorer.proof_scorer emit.)
_RESOURCE_STAGES = frozenset(
    {
        "compile_submission_resource",
        "compile_submission_timeout",
        "compile_submission_oversize",
        "safeverify_resource",
        "safeverify_timeout",
        "submission_oversize",
    }
)


async def gated_incorrect_message(state: AgentState, scores: list[Score]) -> str:
    """Pick the reply for a rejected gated submission.

    Opaque by default; the resource message only when a score's ``stage`` marks a
    too-expensive-to-process failure -- an OOM/timeout/oversize in either
    agent-side step (``state`` is unused -- the verdict is all we need).
    """
    if any((s.metadata or {}).get("stage") in _RESOURCE_STAGES for s in scores):
        return RESOURCE_INCORRECT_MESSAGE
    return INCORRECT_MESSAGE


def _warn_if_ignored_formalizations(state: TaskState) -> None:
    """Warn when this sample's conjecture had more than one upstream formalization.

    The dataset uses the first file and records the rest in
    ``metadata['unused_formalization_files']``. Warning here (run time, per
    evaluated sample) rather than at dataset build keeps it scoped to the
    samples actually run -- not those Inspect drops via ``--sample-id``/``--limit``.
    """
    unused = state.metadata.get("unused_formalization_files")
    if unused:
        logger.warning(
            "Conjecture %s had multiple upstream formalizations; using the "
            "first, ignoring %s. Redundant autoformalization candidates left in "
            "upstream for unknown reason; rare (3/492, only 1 a substantive "
            "difference).",
            state.sample_id,
            ", ".join(unused),
        )


@tool
def submit() -> Tool:
    """A no-argument submit tool.

    The proof is the edited file, not a text answer, so submitting takes no
    arguments -- the model just signals it is done.
    """

    async def execute() -> ToolResult:
        """Submit the proof for verification."""
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
        raise ValueError(
            f"Unknown agent_type {agent_type!r}; expected 'deep' or 'react'."
        )
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

    Writes the initial Lean file (the sample's ``metadata['sketch']``) into the
    sandbox at the entry module ``Submission/Spec.lean`` and runs the agent. The
    proof is the agent's ``Submission/Spec.lean`` (a single file); the scorer
    reads it back from there both to verify it and to record it as a display tree
    on ``state.metadata["submission_contents"]`` (see :mod:`apn.scorer`). The
    capture lives in the scorer, not here, because the scorer always runs after
    the agent -- including when a token/time limit terminates it -- whereas code
    after the agent runs is skipped on a limit.

    Args:
        model: Optional model override for the agent.
        max_attempts: With ``> 1``, enables *gated submit* via Inspect's native
            ``attempts``: each submission is re-scored by the task scorer
            (SafeVerify) and, if not accepted, the model is told to keep going
            (up to this many attempts, or until a token/time limit). With ``1``
            (default), the first submission ends the loop and is validated only
            by the final scorer.
        literature: If true, tell the agent about the offline arXiv corpus at
            ``/corpus`` and run against the agent-corpus image that contains it
            (the task wires the image; the tool set is unchanged -- the agent
            greps ``/corpus`` with its ``bash`` shell). The corpus is a 2022
            snapshot, so it predates the benchmark paper and can't leak a later
            solution. Off by default: it's a literature-augmented run condition,
            reported separately from the closed-book numbers.
        agent_type: Which agent loop to run -- ``"deep"`` for Inspect's
            ``deepagent`` or ``"react"`` for its plain react agent. Both get the
            same tools, gating, submit tool, and prompt; see :func:`build_agent`.
    """

    async def solve(state: TaskState, generate: Generate) -> TaskState:
        _warn_if_ignored_formalizations(state)
        # metadata["sketch"] is the single source of the conjecture spec (set by
        # the dataset; same text the scorer verifies against). The dataset has
        # already stripped the copyright/license banner, so this is written to
        # the entry file as-is.
        sketch = state.metadata["sketch"]
        await sandbox().write_file(ENTRY_PATH, sketch)

        tools = [
            text_editor(),
            # Shell access to the workspace image: the agent drives PyPantograph
            # from python3 to compile the proof file, and the same shell is its
            # numeric scratchpad (sympy/numpy are baked in). On a literature run
            # the same shell also has the offline arXiv corpus at /corpus to grep
            # (the task selects the agent-corpus image; the tool set is the same).
            bash(timeout=300),
            # Lets the agent check how much of its token/time budget remains, so
            # it can self-pace against the configured limits instead of guessing.
            resources(),
        ]

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
        # Seed the conversation with the task prompt, then run the agent *as a
        # solver*. We replace state.messages (rather than append) so the agent
        # sees exactly the prompt -- the sample input is the raw spec text, which
        # is already written to the sandbox file above and would only be
        # duplicative in context. as_solver runs the agent on state.messages and
        # copies the resulting conversation + output back into TaskState in a
        # finally, so the full transcript reaches the sample log (and the
        # viewer's Messages tab) even when a token/time limit terminates the
        # agent -- the common exit for open problems. (Using run() here would run
        # the agent on an isolated state that never propagates back; on a limit
        # it re-raises and the conversation is lost entirely.)
        #
        # The agent authors its proof at Submission/Spec.lean; the scorer reads
        # it back to verify it and to record it as a display tree on the sample
        # metadata (see apn.scorer). The scorer always runs after the
        # agent, including on a limit, whereas any code after the agent call
        # would be skipped on a limit.
        state.messages = [
            ChatMessageUser(
                content=user_prompt(ENTRY_PATH, state.token_limit, literature),
                source="input",
            )
        ]
        state = await as_solver(agent)(state, generate)

        state.completed = True
        return state

    return solve
