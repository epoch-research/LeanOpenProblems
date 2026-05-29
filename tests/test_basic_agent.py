"""Integration tests for the basic agent.

The agent uses Inspect's ``react``/``run`` primitives, which require an active
sample context, so it is exercised through ``eval_async`` on a small task. The
model is Inspect's ``mockllm`` (scripted via a callable) and verification uses
the in-process ``FakeVerifier``, so no real model or Lean sandbox is needed.
"""

from __future__ import annotations

import tempfile

from inspect_ai import Task, eval_async
from inspect_ai.log import EvalLog
from inspect_ai.model import (
    ChatMessage,
    GenerateConfig,
    Model,
    ModelOutput,
    get_model,
)
from inspect_ai.scorer import CORRECT, INCORRECT
from inspect_ai.tool import ToolChoice, ToolInfo

from apn.agents.basic import BasicAgentConfig, basic_agent
from apn.dataset import sketch_sample
from apn.scorer import proof_scorer
from apn.verifier.fake import FakeVerifier

SORRY_SKETCH = (
    "import Mathlib\n"
    "theorem tgt : True := by\n"
    "-- EVOLVE-BLOCK-START\n"
    "  sorry\n"
    "-- EVOLVE-BLOCK-END\n"
)

SOLVED_SKETCH = (
    "import Mathlib\n"
    "theorem tgt : True := by\n"
    "-- EVOLVE-BLOCK-START\n"
    "  trivial\n"
    "-- EVOLVE-BLOCK-END\n"
)


def _solving_model() -> Model:
    """Makes one solving edit per episode, then ends its turn."""

    def respond(
        messages: list[ChatMessage],
        tools: list[ToolInfo],
        tool_choice: ToolChoice,
        config: GenerateConfig,
    ) -> ModelOutput:
        already_edited = any(m.role == "tool" for m in messages)
        if not already_edited:
            return ModelOutput.for_tool_call(
                model="mockllm/model",
                tool_name="search_replace",
                tool_arguments={"search": "  sorry\n", "replace": "  trivial\n"},
            )
        return ModelOutput.from_content(model="mockllm/model", content="Done.")

    return get_model("mockllm/model", custom_outputs=respond)


def _idle_model() -> Model:
    """Never edits; ends its turn immediately."""

    def respond(
        messages: list[ChatMessage],
        tools: list[ToolInfo],
        tool_choice: ToolChoice,
        config: GenerateConfig,
    ) -> ModelOutput:
        return ModelOutput.from_content(model="mockllm/model", content="I give up.")

    return get_model("mockllm/model", custom_outputs=respond)


def _task(sketch_text: str, config: BasicAgentConfig) -> Task:
    verifier = FakeVerifier()
    return Task(
        dataset=[sketch_sample(sketch_text, "t")],
        solver=basic_agent(verifier, config),
        scorer=proof_scorer(verifier),
    )


async def _run(task: Task, model: Model) -> EvalLog:
    logs = await eval_async(task, model=model, log_dir=tempfile.mkdtemp())
    return logs[0]


def _score_value(log: EvalLog) -> object:
    assert log.samples is not None
    scores = log.samples[0].scores
    assert scores is not None
    return scores["proof_scorer"].value


async def test_agent_solves_problem() -> None:
    log = await _run(
        _task(SORRY_SKETCH, BasicAgentConfig(num_subagents=1, max_episodes=3)),
        _solving_model(),
    )
    assert log.status == "success"
    assert _score_value(log) == CORRECT
    assert log.samples is not None
    assert log.samples[0].store.get("success") is True
    assert "trivial" in str(log.samples[0].store.get("final_sketch"))


async def test_agent_already_proved() -> None:
    log = await _run(
        _task(SOLVED_SKETCH, BasicAgentConfig(num_subagents=1)),
        _idle_model(),
    )
    assert _score_value(log) == CORRECT


async def test_agent_fails_when_model_idle() -> None:
    log = await _run(
        _task(SORRY_SKETCH, BasicAgentConfig(num_subagents=2, max_episodes=2)),
        _idle_model(),
    )
    assert log.status == "success"  # the eval ran fine; the proof just failed
    assert _score_value(log) == INCORRECT


async def test_multiple_subagents_one_solves() -> None:
    log = await _run(
        _task(SORRY_SKETCH, BasicAgentConfig(num_subagents=3, max_episodes=3)),
        _solving_model(),
    )
    assert _score_value(log) == CORRECT
