"""The basic agent (A).

Mirrors the paper's Figure 1 pseudocode and the "Basic Agent" methods section:

* A *prover subagent* runs a "Ralph loop" of episodes (:func:`run_subagent`).
* Each *episode* is a multi-turn LLM session with the ``search_replace`` tool,
  with Lean compiler feedback after every edit (:func:`run_episode`). When the
  session ends, the sketch is validated with SafeVerify.
* ``N`` subagents run independently with no shared state; the first to produce a
  validated, sorry-free proof wins and the rest are cancelled
  (:func:`run_basic_agent`).

The episode-end handling follows the paper: if validation succeeds and the
proof is sorry-free, it is returned; if a ``sorry`` remains, the next episode
starts from the current sketch (the model is prompted to leave its findings as
comments inside the editable regions, which carry forward); if validation fails
(e.g. an injected axiom), the subagent reverts to the previous sketch.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

import anyio

from inspect_ai.agent import Agent, AgentState, agent, react, run
from inspect_ai.model import Model, ModelOutput, get_model
from inspect_ai.solver import Generate, Solver, TaskState, solver
from inspect_ai.util import message_limit

from apn.prompts import render_basic_prompt
from apn.safeverify import DEFAULT_ALLOWED_AXIOMS, ValidationVerdict, safe_verify
from apn.sketch import ProofSketch
from apn.tools import EpisodeState, search_replace
from apn.verifier.base import LeanVerifier


@dataclass(frozen=True)
class BasicAgentConfig:
    """Search budget for the basic agent.

    Defaults are modest so a run is affordable; the paper evaluated the basic
    agent with up to ``num_subagents=100``.
    """

    num_subagents: int = 4
    max_episodes: int = 10
    max_turns_per_episode: int = 40
    max_edits_per_episode: int = 90
    allowed_axioms: frozenset[str] = DEFAULT_ALLOWED_AXIOMS
    model: str | None = None


@dataclass
class ProofResult:
    success: bool
    sketch: ProofSketch
    verdict: ValidationVerdict | None = None
    episodes: int = 0
    subagent_index: int | None = None


async def run_episode(
    model: Model,
    verifier: LeanVerifier,
    sketch: ProofSketch,
    original: ProofSketch,
    target_declarations: list[str],
    *,
    max_turns: int,
    max_edits: int,
    allowed_axioms: frozenset[str] = DEFAULT_ALLOWED_AXIOMS,
) -> tuple[ProofSketch, ValidationVerdict]:
    """Run one proving episode and validate the result.

    The episode is a built-in ``react`` agent run with ``submit=False``: it loops
    "generate -> run search_replace -> feed compiler output back" and terminates
    exactly when the model stops calling tools (matching the paper's session that
    ends when the prover emits no further edits). It is bounded by a message
    limit derived from ``max_turns``; ``max_edits`` is enforced by the tool. The
    edited sketch is read back from the tool's ``EpisodeState`` afterwards.

    Returns the (possibly edited) sketch and its SafeVerify verdict.
    """
    episode_state = EpisodeState(
        sketch=sketch, verifier=verifier, max_edits=max_edits
    )
    tool = search_replace(episode_state)
    episode_agent = react(
        prompt=None,  # the full paper prompt is supplied as the input message
        tools=[tool],
        model=model,
        submit=False,
        truncation="auto",
    )
    # Each turn adds an assistant message and (usually) a tool message, so allow
    # roughly two messages per turn plus the initial prompt.
    await run(
        episode_agent,
        render_basic_prompt(sketch.text),
        limits=[message_limit(2 * max_turns + 2)],
    )

    verdict = await safe_verify(
        verifier,
        original,
        episode_state.sketch,
        target_declarations,
        allowed_axioms=allowed_axioms,
    )
    return episode_state.sketch, verdict


async def run_subagent(
    index: int,
    model: Model,
    verifier: LeanVerifier,
    original: ProofSketch,
    target_declarations: list[str],
    config: BasicAgentConfig,
) -> ProofResult:
    """Run one prover subagent's Ralph loop of episodes."""
    sketch = original
    last_verdict: ValidationVerdict | None = None
    episode = 0
    while episode < config.max_episodes and sketch.contains_sorry():
        episode += 1
        new_sketch, verdict = await run_episode(
            model,
            verifier,
            sketch,
            original,
            target_declarations,
            max_turns=config.max_turns_per_episode,
            max_edits=config.max_edits_per_episode,
            allowed_axioms=config.allowed_axioms,
        )
        if verdict.passes_validation:
            # Validation passed: adopt the new sketch.
            sketch = new_sketch
            last_verdict = verdict
            if verdict.is_complete_proof:
                return ProofResult(
                    success=True,
                    sketch=sketch,
                    verdict=verdict,
                    episodes=episode,
                    subagent_index=index,
                )
        # Validation failed: revert (keep the previous `sketch`), but remember
        # the verdict for diagnostics.
        elif last_verdict is None:
            last_verdict = verdict
    return ProofResult(
        success=False,
        sketch=sketch,
        verdict=last_verdict,
        episodes=episode,
        subagent_index=index,
    )


@agent
def prover_subagent(
    model: Model,
    verifier: LeanVerifier,
    original: ProofSketch,
    target_declarations: list[str],
    config: BasicAgentConfig,
) -> Agent:
    """A prover subagent as an Inspect agent.

    Wrapping :func:`run_subagent` as an ``@agent`` lets the orchestrator launch
    each subagent with :func:`inspect_ai.agent.run`, which copies the input,
    isolates it, and records a dedicated span in the transcript. The subagent
    writes its :class:`ProofResult` into the shared ``results`` mapping (the
    subagents coordinate no proof state with each other; ``results`` is only a
    sink for the orchestrator).
    """

    async def execute(
        state: AgentState,
        *,
        index: int,
        results: dict[int, ProofResult],
    ) -> AgentState:
        result = await run_subagent(
            index, model, verifier, original, target_declarations, config
        )
        results[index] = result
        state.output = ModelOutput.from_content(
            model=model.name, content=result.sketch.text
        )
        return state

    return execute


async def run_basic_agent(
    model: Model,
    verifier: LeanVerifier,
    original: ProofSketch,
    target_declarations: list[str],
    config: BasicAgentConfig | None = None,
) -> ProofResult:
    """Run ``N`` independent subagents; the first complete proof wins.

    Each subagent is launched via :func:`inspect_ai.agent.run`. When one
    succeeds, the surrounding task group is cancelled so the others stop
    immediately (the paper terminates all other subagents as soon as one finds a
    proof).
    """
    cfg = config or BasicAgentConfig()
    if not original.contains_sorry():
        # Nothing to prove; validate the provided file as-is.
        verdict = await safe_verify(
            verifier, original, original, target_declarations,
            allowed_axioms=cfg.allowed_axioms,
        )
        return ProofResult(success=verdict.is_complete_proof, sketch=original, verdict=verdict)

    subagent = prover_subagent(model, verifier, original, target_declarations, cfg)
    initial_input = render_basic_prompt(original.text)
    results: dict[int, ProofResult] = {}
    winner: ProofResult | None = None

    async with anyio.create_task_group() as tg:

        async def worker(i: int) -> None:
            nonlocal winner
            await run(subagent, initial_input, index=i, results=results)
            result = results.get(i)
            if result is not None and result.success and winner is None:
                winner = result
                tg.cancel_scope.cancel()

        for i in range(cfg.num_subagents):
            tg.start_soon(worker, i)

    if winner is not None:
        return winner
    return _best_partial(results.values(), original)


def _best_partial(results: Iterable[ProofResult], original: ProofSketch) -> ProofResult:
    """Pick the most promising non-winning result for reporting."""
    candidates = list(results)
    if not candidates:
        return ProofResult(success=False, sketch=original)
    # Prefer a result that at least passed validation (compiles, statement
    # intact, no injected axioms), then the earliest subagent.
    candidates.sort(
        key=lambda r: (
            0 if (r.verdict is not None and r.verdict.passes_validation) else 1,
            r.subagent_index if r.subagent_index is not None else 1_000_000,
        )
    )
    return candidates[0]


@solver
def basic_agent(
    verifier: LeanVerifier, config: BasicAgentConfig | None = None
) -> Solver:
    """The basic agent (A) as an Inspect solver.

    Reads the initial Lean sketch from the sample (``metadata['sketch']`` if
    present, else the sample input text) and the target theorem name(s) from
    ``metadata['target_declarations']``. Writes the final sketch, success flag,
    and validation verdict into the sample store for the scorer.
    """
    cfg = config or BasicAgentConfig()

    async def solve(state: TaskState, generate: Generate) -> TaskState:
        model = get_model(cfg.model) if cfg.model is not None else get_model()
        sketch_text = state.metadata.get("sketch") or state.input_text
        original = ProofSketch(sketch_text)
        target_declarations = list(state.metadata.get("target_declarations", []))

        result = await run_basic_agent(
            model, verifier, original, target_declarations, cfg
        )

        store = state.store
        store.set("success", result.success)
        store.set("final_sketch", result.sketch.text)
        store.set("episodes", result.episodes)
        store.set("subagent_index", result.subagent_index)
        if result.verdict is not None:
            store.set("verdict", _verdict_to_dict(result.verdict))

        state.output = ModelOutput.from_content(
            model=str(state.model), content=result.sketch.text
        )
        state.completed = True
        return state

    return solve


def _verdict_to_dict(verdict: ValidationVerdict) -> dict[str, object]:
    return {
        "compiles": verdict.compiles,
        "statement_preserved": verdict.statement_preserved,
        "has_sorry": verdict.has_sorry,
        "uses_sorry_ax": verdict.uses_sorry_ax,
        "disallowed_axioms": list(verdict.disallowed_axioms),
        "passes_validation": verdict.passes_validation,
        "is_complete_proof": verdict.is_complete_proof,
    }
