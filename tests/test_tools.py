"""Tests for the search_replace tool and the basic-agent prompt."""

from __future__ import annotations

import pytest

from apn.prompts import render_basic_prompt
from apn.sketch import ProofSketch
from apn.tools import EpisodeState, search_replace
from apn.verifier.base import CompileResult, Diagnostic
from apn.verifier.fake import FakeVerifier

SAMPLE = (
    "import Mathlib\n"
    "theorem tgt : True := by\n"
    "-- EVOLVE-BLOCK-START\n"
    "  sorry\n"
    "-- EVOLVE-BLOCK-END\n"
)


def _state(**kwargs: object) -> EpisodeState:
    return EpisodeState(sketch=ProofSketch(SAMPLE), verifier=FakeVerifier(), **kwargs)  # type: ignore[arg-type]


async def test_search_replace_applies_and_compiles() -> None:
    state = _state()
    tool = search_replace(state)
    feedback = await tool(search="  sorry\n", replace="  trivial\n")
    assert "trivial" in state.sketch.text
    assert state.edits == 1
    assert state.last_compile is not None and state.last_compile.ok
    assert isinstance(feedback, str)


async def test_search_replace_keeps_failing_edit() -> None:
    # A compile error does not revert the edit; the model fixes it next turn.
    def compile_fn(code: str) -> CompileResult:
        return CompileResult(diagnostics=(Diagnostic("error", "boom", 3),))

    state = EpisodeState(sketch=ProofSketch(SAMPLE), verifier=FakeVerifier(compile_fn=compile_fn))
    tool = search_replace(state)
    feedback = await tool(search="  sorry\n", replace="  bad\n")
    assert "bad" in state.sketch.text
    assert isinstance(feedback, str)
    assert "boom" in feedback


async def test_search_replace_rejects_out_of_region() -> None:
    from inspect_ai.tool import ToolError

    state = _state()
    tool = search_replace(state)
    with pytest.raises(ToolError):
        await tool(search="True", replace="False")
    assert state.edits == 0


async def test_edit_budget_enforced() -> None:
    from inspect_ai.tool import ToolError

    state = _state(max_edits=1)
    tool = search_replace(state)
    await tool(search="  sorry\n", replace="  trivial\n")
    with pytest.raises(ToolError, match="budget"):
        await tool(search="trivial", replace="rfl")


def test_render_basic_prompt() -> None:
    rendered = render_basic_prompt(SAMPLE)
    assert "world-class mathematician" in rendered
    assert "theorem tgt : True" in rendered
    assert "{code}" not in rendered
    assert "EVOLVE-BLOCK-START" in rendered
