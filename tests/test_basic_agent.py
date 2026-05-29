"""Integration test for the basic agent.

The agent uses Inspect's ``text_editor`` tool, which injects into a Linux
container, so it cannot run against the macOS ``local`` sandbox. This test is
therefore gated on Docker plus the prebuilt ``apn-lean`` image. It exercises the
full orchestration (per-subagent sandbox, ``text_editor`` edits via the real
container filesystem, the episode loop, SafeVerify) with a scripted ``mockllm``
model and the in-process ``FakeVerifier`` so no real model or Lean is needed.
"""

from __future__ import annotations

import shutil
import subprocess
import tempfile

import pytest

from inspect_ai import Task, eval_async
from inspect_ai.dataset import Sample
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

from apn.agents.basic import PROOF_PATH, BasicAgentConfig, basic_agent
from apn.dataset import sketch_sample
from apn.scorer import proof_scorer
from apn.task import _generate_compose
from apn.verifier.fake import FakeVerifier


def _docker_ready() -> bool:
    if shutil.which("docker") is None:
        return False
    try:
        result = subprocess.run(
            ["docker", "image", "inspect", "apn-lean"],
            capture_output=True,
            timeout=30,
        )
        return result.returncode == 0
    except Exception:
        return False


pytestmark = pytest.mark.skipif(
    not _docker_ready(), reason="requires docker and the apn-lean image"
)

SORRY_SKETCH = (
    "import Mathlib\n"
    "theorem tgt : True := by\n"
    "-- EVOLVE-BLOCK-START\n"
    "  sorry\n"
    "-- EVOLVE-BLOCK-END\n"
)


def _editor_model() -> Model:
    """Edits the proof file once via text_editor, then ends its turn."""

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
                tool_name="text_editor",
                tool_arguments={
                    "command": "str_replace",
                    "path": PROOF_PATH,
                    "old_str": "  sorry",
                    "new_str": "  trivial",
                },
            )
        return ModelOutput.from_content(model="mockllm/model", content="Done.")

    return get_model("mockllm/model", custom_outputs=respond)


def _idle_model() -> Model:
    def respond(
        messages: list[ChatMessage],
        tools: list[ToolInfo],
        tool_choice: ToolChoice,
        config: GenerateConfig,
    ) -> ModelOutput:
        return ModelOutput.from_content(model="mockllm/model", content="I give up.")

    return get_model("mockllm/model", custom_outputs=respond)


def _task(num_subagents: int) -> Task:
    verifier = FakeVerifier()
    return Task(
        dataset=[sketch_sample(SORRY_SKETCH, "tgt")],
        solver=basic_agent(
            verifier, BasicAgentConfig(num_subagents=num_subagents, max_episodes=2)
        ),
        scorer=proof_scorer(verifier),
        sandbox=("docker", _generate_compose(num_subagents)),
    )


async def _run(task: Task, model: Model) -> EvalLog:
    logs = await eval_async(task, model=model, log_dir=tempfile.mkdtemp())
    return logs[0]


@pytest.mark.slow
async def test_agent_solves_via_text_editor() -> None:
    log = await _run(_task(num_subagents=1), _editor_model())
    assert log.status == "success"
    assert log.samples is not None
    assert log.samples[0].scores is not None
    assert log.samples[0].scores["proof_scorer"].value == CORRECT
    assert "trivial" in str(log.samples[0].store.get("final_sketch"))


@pytest.mark.slow
async def test_agent_fails_when_idle() -> None:
    log = await _run(_task(num_subagents=1), _idle_model())
    assert log.status == "success"
    assert log.samples is not None
    assert log.samples[0].scores is not None
    assert log.samples[0].scores["proof_scorer"].value == INCORRECT
