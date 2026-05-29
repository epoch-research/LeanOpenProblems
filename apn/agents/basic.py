"""The basic agent (A).

Mirrors the paper's Figure 1 pseudocode and the "Basic Agent" methods section:

* A *prover subagent* runs a "Ralph loop" of episodes (:func:`run_subagent`).
* Each *episode* is a multi-turn LLM session in which the model edits a Lean file
  with Inspect's built-in ``text_editor`` tool and compiles it with
  ``lean_check`` (:func:`run_episode`). The session ends when the model stops
  calling tools; the resulting sketch is then validated with SafeVerify.
* The subagents run independently with no shared state; **each gets its own Lean
  sandbox** (one Docker service per subagent). The first to produce a validated,
  ``sorry``-free proof wins and the rest are cancelled (:func:`run_basic_agent`).

Episode-end handling follows the paper: if validation succeeds and the proof is
``sorry``-free, it is returned; if a ``sorry`` remains, the next episode starts
from the current sketch (the model leaves its findings as comments inside the
editable regions, which carry forward); if validation fails (e.g. an out-of-
region edit or an injected axiom), the subagent reverts to the previous sketch.
"""

from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
from typing import Iterable, Iterator

import anyio

from inspect_ai.agent import Agent, AgentState, agent, react, run
from inspect_ai.model import Model, ModelOutput, get_model
from inspect_ai.solver import Generate, Solver, TaskState, solver
from inspect_ai.tool import text_editor
from inspect_ai.util import message_limit, sandbox
from inspect_ai.util._sandbox.context import sandbox_environments_context_var

from apn.prompts import render_basic_prompt
from apn.safeverify import DEFAULT_ALLOWED_AXIOMS, ValidationVerdict, safe_verify
from apn.sketch import ProofSketch
from apn.tools import lean_check
from apn.verifier.base import LeanVerifier

# Path of the proof file inside each subagent's sandbox. A constant is fine
# because every subagent has its own isolated sandbox.
PROOF_PATH = "/tmp/apn_proof.lean"


@dataclass(frozen=True)
class BasicAgentConfig:
    """Search budget for the basic agent.

    ``num_subagents`` determines how many Lean sandboxes are provisioned (one per
    subagent). Defaults are modest so a run is affordable; the paper evaluated
    the basic agent with up to ``num_subagents=100``.
    """

    num_subagents: int = 4
    max_episodes: int = 10
    max_turns_per_episode: int = 40
    allowed_axioms: frozenset[str] = DEFAULT_ALLOWED_AXIOMS
    model: str | None = None


@dataclass
class ProofResult:
    success: bool
    sketch: ProofSketch
    verdict: ValidationVerdict | None = None
    episodes: int = 0
    subagent_index: int | None = None


@contextmanager
def _only_sandbox(name: str | None) -> Iterator[None]:
    """Restrict the visible sandbox environments to a single named one.

    The built-in ``text_editor`` tool injects into whichever sandbox it finds
    first, so to pin a subagent to its own sandbox we scope the per-sample
    environment map down to that one environment for the duration of the
    subagent. This runs in the subagent's own task, so the context change is
    isolated to it.
    """
    if name is None:
        yield
        return
    environments = sandbox_environments_context_var.get(None)
    if not environments or name not in environments:
        yield
        return
    token = sandbox_environments_context_var.set({name: environments[name]})
    try:
        yield
    finally:
        sandbox_environments_context_var.reset(token)


async def run_episode(
    model: Model,
    verifier: LeanVerifier,
    sketch: ProofSketch,
    original: ProofSketch,
    target_declarations: list[str],
    *,
    path: str = PROOF_PATH,
    max_turns: int,
    allowed_axioms: frozenset[str] = DEFAULT_ALLOWED_AXIOMS,
) -> tuple[ProofSketch, ValidationVerdict]:
    """Run one proving episode and validate the result.

    The episode is a built-in ``react`` agent run with ``submit=False``: it loops
    "edit with text_editor -> lean_check" and terminates when the model stops
    calling tools (matching the paper's session that ends when the prover emits
    no further edits), bounded by a message limit derived from ``max_turns``. The
    sketch is written to ``path`` in the current sandbox beforehand and read back
    afterwards.

    Returns the (possibly edited) sketch and its SafeVerify verdict.
    """
    sb = sandbox()
    await sb.write_file(path, sketch.text)

    episode_agent = react(
        prompt=None,  # the full paper prompt is supplied as the input message
        tools=[text_editor(), lean_check(verifier, path)],
        model=model,
        submit=False,
        truncation="auto",
    )
    await run(
        episode_agent,
        render_basic_prompt(sketch.text, path),
        limits=[message_limit(2 * max_turns + 2)],
    )

    candidate = ProofSketch(await sb.read_file(path))
    verdict = await safe_verify(
        verifier, original, candidate, target_declarations, allowed_axioms=allowed_axioms
    )
    return candidate, verdict


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
        elif last_verdict is None:
            # Validation failed: revert (keep the previous sketch); remember the
            # verdict for diagnostics.
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
    """A prover subagent as an Inspect agent, pinned to its own sandbox.

    Launched with :func:`inspect_ai.agent.run` (its own transcript span and
    isolated state). It writes its :class:`ProofResult` into the shared
    ``results`` mapping; the subagents share no proof state with each other.
    """

    async def execute(
        state: AgentState,
        *,
        index: int,
        results: dict[int, ProofResult],
        sandbox_name: str | None = None,
    ) -> AgentState:
        with _only_sandbox(sandbox_name):
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
    """Run one subagent per Lean sandbox; the first complete proof wins.

    The number of subagents equals the number of sandbox environments provisioned
    for the sample (see :func:`apn.task.apn_basic`). When a subagent succeeds, the
    surrounding task group is cancelled so the others stop immediately.
    """
    cfg = config or BasicAgentConfig()
    if not original.contains_sorry():
        verdict = await safe_verify(
            verifier, original, original, target_declarations,
            allowed_axioms=cfg.allowed_axioms,
        )
        return ProofResult(
            success=verdict.is_complete_proof, sketch=original, verdict=verdict
        )

    environments = sandbox_environments_context_var.get(None) or {}
    sandbox_names: list[str | None] = list(environments.keys()) or [None]

    subagent = prover_subagent(model, verifier, original, target_declarations, cfg)
    results: dict[int, ProofResult] = {}
    winner: ProofResult | None = None

    async with anyio.create_task_group() as tg:

        async def worker(i: int, name: str | None) -> None:
            nonlocal winner
            await run(
                subagent,
                original.text,
                index=i,
                results=results,
                sandbox_name=name,
            )
            result = results.get(i)
            if result is not None and result.success and winner is None:
                winner = result
                tg.cancel_scope.cancel()

        for i, name in enumerate(sandbox_names):
            tg.start_soon(worker, i, name)

    if winner is not None:
        return winner
    return _best_partial(results.values(), original)


def _best_partial(results: Iterable[ProofResult], original: ProofSketch) -> ProofResult:
    """Pick the most promising non-winning result for reporting."""
    candidates = list(results)
    if not candidates:
        return ProofResult(success=False, sketch=original)
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
