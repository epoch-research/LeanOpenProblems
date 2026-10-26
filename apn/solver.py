from __future__ import annotations

import logging
from typing import Any, Callable, Literal, Sequence

from inspect_ai.agent import (
    Agent,
    AgentAttempts,
    AgentContinue,
    AgentState,
    AgentSubmit,
    agent,
    as_solver,
    deepagent,
    general,
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
from inspect_ai.util import sandbox, store
from inspect_boltons.tools import resources
from inspect_swarm import (
    Budget,
    member,
    shared_memory,
    swarm,
    swarm_on_continue,
    swarm_resources,
    swarm_tools,
)

from apn.checker import Claim, comparator_sandbox_name
from apn.layout import ENTRY_PATH
from apn.limits import continue_unless_looping
from apn.prompts import user_prompt
from apn.scorer import claim_store_key
from apn.tools import bash

logger = logging.getLogger(__name__)

# Deliberately reveals nothing about *why* (no verifier output), so the model
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
        "comparator_output_limit",
        "comparator_resource",
        "comparator_timeout",
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
    ``metadata['other_sources']``. Warning here (run time, per evaluated
    sample) rather than at dataset build keeps it scoped to the samples
    actually run, not those Inspect drops via ``--sample-id``/``--limit``.
    """
    unused = state.metadata.get("other_sources")
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
    """The submit tool: the agent declares its claim, nothing else.

    The claim (proof vs disproof) selects which of the spec's two theorems the
    checker verifies (``foo`` or ``foo.disproof``); the scorer reads it from
    the sample store. There is no sniffing of submission content -- a wrong
    declaration simply fails its check like any wrong submission. Inspect's
    tool-argument validation rejects a malformed call before it reaches us, so
    the model retries rather than submitting nothing.
    """

    async def execute(claim: Claim) -> ToolResult:
        """Submit the proof for verification.

        Args:
            claim: "proof" if you proved the original theorem, "disproof" if
                you proved its `.disproof` negation.
        """
        if claim not in ("proof", "disproof"):
            raise ValueError(f'claim must be "proof" or "disproof", got {claim!r}')
        store().set(claim_store_key(), claim)
        return "Submitted."

    return execute


AgentType = Literal["deep", "react"]


def _attempts(gated: bool) -> AgentAttempts:
    # An effectively infinite max_attempts on the built-in Inspect react() and deepagent()
    # solvers is used to implement "gated submission" (Inspect allows retries if the scorer
    # returns INCORRECT). This is a bit of a hack: it would be clearer to implement this
    # inside the solver. However, doing it like this lets us benefit automatically from
    # upstream improvements in the built-in solvers; in particular, Inspect maintainers will
    # keep these up to date with internal Inspect changes.
    max_attempts = 99_999_999 if gated else 1
    return AgentAttempts(
        attempts=max_attempts, incorrect_message=gated_incorrect_message
    )


def _prover_submit() -> AgentSubmit:
    # Name it distinctly from any subagents' "submit" tool and keep the
    # call in the message history. keep_in_messages=True stops the loop
    # from folding the tool's return into the assistant message; the
    # distinct name means the main loop's submission scan can never match
    # a subagent's "submit" (no early-termination collision).
    return AgentSubmit(tool=submit(), name="submit_proof", keep_in_messages=True)


# The default continue message is very generic ("proceed to the next step"), this one
# might be better at avoiding doom loops.
CONTINUE_MESSAGE = "Continue working on the problem."


def swarm_member_names(swarm_size: int | None) -> list[str] | None:
    """The swarm's member names, or ``None`` for no swarm (``swarm_size`` unset,
    zero or negative)."""
    if swarm_size is None or swarm_size <= 0:
        return None
    return [f"prover-{i}" for i in range(1, swarm_size + 1)]


def build_agent(
    agent_type: AgentType,
    *,
    tools: Sequence[Tool | ToolDef | ToolSource],
    attempts: AgentAttempts,
    submit: AgentSubmit,
    on_continue: AgentContinue,
    compaction: CompactionStrategy,
) -> Agent:
    """Construct the configured agent loop.

    Only exposes functionality common to ``deepagent`` and ``react`` so the two
    behave identically apart from the loop itself. The one ``deepagent``-only
    setting is the subagent roster, restricted to ``general()``.
    """
    constructor: Callable[..., Agent]
    loop_kwargs: dict[str, Any] = {}
    if agent_type == "deep":
        constructor = deepagent
        # deepagent() defaults to [research(), plan(), general()]. Only
        # general() inherits the parent's tools (text_editor, bash, resources);
        # research() and plan() default to read-only sandbox tools (read_file,
        # list_files, grep), and this is not made clear to agents.
        loop_kwargs["subagents"] = [general()]
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
        **loop_kwargs,
    )


@agent
def _prover(agent_type: AgentType, gated: bool, swarm: bool = False) -> Agent:
    """The prover loop, for a single agent or a swarm member.

    ``swarm_tools()`` and ``swarm_on_continue()`` do nothing outside a swarm. A
    member's budget tool is ``swarm_resources`` (its own share of the budget),
    since ``resources`` shows the sample's limits."""
    return build_agent(
        agent_type,
        tools=[
            text_editor(),
            bash(timeout=300),
            # TODO: make inspect_boltons' resources() report a swarm member's own
            #   budget via swarm_budget() (started on tadamcz/inspect_boltons branch
            #   swarm-aware-resources), then use it for everyone and drop this helper function.
            swarm_resources() if swarm else resources(),
            swarm_tools(),
        ],
        attempts=_attempts(gated),
        submit=_prover_submit(),
        on_continue=swarm_on_continue(continue_unless_looping(CONTINUE_MESSAGE)),
        compaction=CompactionSummary(threshold=300_000),
    )


@solver
def lean_prover(
    agent_type: AgentType,
    gated: bool,
    literature: bool,
    util_module: str,
    swarm_size: int | None = None,
) -> Solver:
    """
    Args:
        gated: Gated submission (retry until correct or token/time limit).
        literature: Run with the offline arXiv corpus.
        agent_type: Which agent loop to run (each member's, in a swarm).
        util_module: The dataset pin's FC util module
            (``apn.dataset.fc_profile(...).util_module``), named in the prompt's
            import-integrity rule.
        swarm_size: Run a swarm of this many members; ``None``, zero or
            negative runs a single agent. Each member works in its own sandbox
            (see ``swarm_member_names``) with its own comparator; the swarm's
            budget is split equally.
    """

    async def solve(state: TaskState, generate: Generate) -> TaskState:
        _warn_if_ignored_formalizations(state)
        sketch = state.metadata["sketch"]

        names = swarm_member_names(swarm_size)
        if names is not None:
            for name in names:
                await sandbox(name).write_file(ENTRY_PATH, sketch)
            agent = swarm(
                members=[
                    member(
                        _prover,
                        name=name,
                        args={"agent_type": agent_type, "gated": gated, "swarm": True},
                        sandbox=name,
                        visible_sandboxes=[comparator_sandbox_name(name)],
                    )
                    for name in names
                ],
                channels=[shared_memory(
                    # TODO: remove these if inspect_swarm changes their defaults to be more sensible
                    # TODO: raise max_file_bytes and max_board_bytes (set at inspect_swarm's
                    # current caps) once the upstream PR removing the caps is released
                    max_files=10_000,
                    max_file_bytes=262_144,
                    max_file_lines=100_000,
                    max_board_bytes=16_777_216,
                )],
                budget=Budget(split="equal"),
            )
        else:
            await sandbox().write_file(ENTRY_PATH, sketch)
            agent = _prover(agent_type, gated)
        state.messages = [
            ChatMessageUser(
                content=user_prompt(ENTRY_PATH, state.token_limit, literature, util_module),
                source="input",
            )
        ]
        state = await as_solver(agent)(state, generate)

        state.completed = True
        return state

    return solve
