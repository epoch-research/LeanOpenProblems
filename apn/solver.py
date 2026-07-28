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
)
from inspect_ai.scorer import Score
from inspect_ai.solver import Generate, Solver, TaskState, solver
from inspect_ai.tool import Tool, ToolDef, ToolResult, ToolSource, text_editor, tool
from inspect_ai.util import sandbox

from apn.layout import ENTRY_PATH
from apn.prompts import user_prompt
from apn.tools import bash, resources

logger = logging.getLogger(__name__)

# Deliberately reveals nothing about *why* (no SafeVerify output), so the model
# cannot search for verifier gaps.
INCORRECT_MESSAGE = (
    "Your submission did not pass verification. Keep working to find a correct, "
    "complete proof."
)

# The one exception to the opaque policy: when the submission was too expensive
# to process (rather than rejected on the merits) tell the model that much, but nothing more.
RESOURCE_INCORRECT_MESSAGE = (
    "Checking your submission exceeded a resource limit (it "
    "ran out of memory, timed out, or created files that were too large). Keep working to find a "
    "correct, complete proof that is cheaper to check."
)

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
    if any((s.metadata or {}).get("stage") in _RESOURCE_STAGES for s in scores):
        return RESOURCE_INCORRECT_MESSAGE
    return INCORRECT_MESSAGE


def _warn_if_ignored_formalizations(state: TaskState) -> None:
    """Warn when this sample's conjecture had more than one upstream formalization.

    The dataset uses the first file and records the rest in
    ``metadata['unused_formalization_files']``. Warning here (run time, per
    evaluated sample) rather than at dataset build keeps it scoped to the
    samples actually run, not those Inspect drops via ``--sample-id``/``--limit``.
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
    """A no-argument submit tool."""

    async def execute() -> ToolResult:
        """Submit the proof for verification."""
        return "Submitted."

    return execute


AgentType = Literal["deep", "react"]


def build_agent(
    agent_type: AgentType,
    *,
    tools: Sequence[Tool | ToolDef | ToolSource],
    attempts: AgentAttempts,
    submit: AgentSubmit,
    on_continue: str,
    compaction: CompactionStrategy,
) -> Agent:
    """Construct the configured agent loop.

    Only exposes functionality common to ``deepagent`` and ``react`` so the two
    behave identically apart from the loop itself
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

    # everything else left at default
    return constructor(
        tools=tools,
        attempts=attempts,
        submit=submit,
        on_continue=on_continue,
        compaction=compaction,
    )


@solver
def lean_prover(
    agent_type: AgentType,
    gated: bool,
    literature: bool,
) -> Solver:
    """
    Args:
        gated: Gated submission (retry until correct or token/time limit).
        literature: Run with the offline arXiv corpus.
        agent_type: Which agent loop to run.
    """

    async def solve(state: TaskState, generate: Generate) -> TaskState:
        _warn_if_ignored_formalizations(state)
        sketch = state.metadata["sketch"]
        await sandbox().write_file(ENTRY_PATH, sketch)

        tools = [
            text_editor(),
            bash(timeout=300),
            resources(),
        ]

        # An effectively infinite max_attempts on the built-in Inspect react() and deepagent()
        # solvers is used to implement "gated submission" (Inspect allows retries if the scorer
        # returns INCORRECT). This is a bit of a hack: it would be clearer to implement this
        # inside the solver. However, doing it like this lets us benefit automatically from
        # upstream improvements in the built-in solvers; in particular, Inspect maintainers will
        # keep these up to date with internal Inspect changes.
        if gated:
            max_attempts = 99_999_999
        else:
            max_attempts = 1

        agent = build_agent(
            agent_type,
            tools=tools,
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
        )
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
