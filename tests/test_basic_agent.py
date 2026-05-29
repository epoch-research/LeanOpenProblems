"""Tests for the basic agent's episode and Ralph-loop orchestration.

Uses Inspect's ``mockllm`` provider to script model outputs and the in-process
``FakeVerifier`` so the whole loop runs deterministically without a real model
or the Lean sandbox.
"""

from __future__ import annotations

from typing import Sequence

from inspect_ai.model import (
    ChatMessage,
    GenerateConfig,
    Model,
    ModelOutput,
    get_model,
)
from inspect_ai.tool import ToolChoice, ToolInfo

from apn.agents.basic import (
    BasicAgentConfig,
    run_basic_agent,
    run_episode,
    run_subagent,
)
from apn.sketch import ProofSketch
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


def _edit_then_stop_model() -> Model:
    """A model that makes one solving edit, then ends its turn."""
    outputs = [
        ModelOutput.for_tool_call(
            model="mockllm/model",
            tool_name="search_replace",
            tool_arguments={"search": "  sorry\n", "replace": "  trivial\n"},
        ),
        ModelOutput.from_content(model="mockllm/model", content="Done; it compiles."),
    ]
    return get_model("mockllm/model", custom_outputs=outputs)


def _never_edits_model() -> Model:
    """A model that always ends its turn without editing."""

    def respond(
        messages: list[ChatMessage],
        tools: list[ToolInfo],
        tool_choice: ToolChoice,
        config: GenerateConfig,
    ) -> ModelOutput:
        return ModelOutput.from_content(model="mockllm/model", content="I give up.")

    return get_model("mockllm/model", custom_outputs=respond)


async def test_run_episode_solves() -> None:
    model = _edit_then_stop_model()
    sketch = ProofSketch(SORRY_SKETCH)
    final, verdict = await run_episode(
        model,
        FakeVerifier(),
        sketch,
        sketch,
        ["tgt"],
        max_turns=10,
        max_edits=90,
    )
    assert "trivial" in final.text
    assert verdict.is_complete_proof


async def test_run_subagent_success() -> None:
    result = await run_subagent(
        0,
        _edit_then_stop_model(),
        FakeVerifier(),
        ProofSketch(SORRY_SKETCH),
        ["tgt"],
        BasicAgentConfig(max_episodes=3),
    )
    assert result.success
    assert result.episodes == 1
    assert result.subagent_index == 0


async def test_run_basic_agent_success_single_subagent() -> None:
    result = await run_basic_agent(
        _edit_then_stop_model(),
        FakeVerifier(),
        ProofSketch(SORRY_SKETCH),
        ["tgt"],
        BasicAgentConfig(num_subagents=1, max_episodes=3),
    )
    assert result.success
    assert "trivial" in result.sketch.text


async def test_run_basic_agent_already_proved() -> None:
    # No sorry to begin with: the agent validates the file without calling a model.
    result = await run_basic_agent(
        _never_edits_model(),
        FakeVerifier(),
        ProofSketch(SOLVED_SKETCH),
        ["tgt"],
        BasicAgentConfig(num_subagents=1),
    )
    assert result.success


async def test_run_basic_agent_failure() -> None:
    result = await run_basic_agent(
        _never_edits_model(),
        FakeVerifier(),
        ProofSketch(SORRY_SKETCH),
        ["tgt"],
        BasicAgentConfig(num_subagents=2, max_episodes=2),
    )
    assert not result.success
    assert result.sketch.contains_sorry()
