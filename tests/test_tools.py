"""Tests for the lean_check feedback formatting and the basic-agent prompt."""

from __future__ import annotations

from apn.prompts import render_basic_prompt
from apn.tools import format_check_feedback
from apn.verifier.base import CompileResult, Diagnostic

SAMPLE = (
    "import Mathlib\n"
    "theorem tgt : True := by\n"
    "-- EVOLVE-BLOCK-START\n"
    "  sorry\n"
    "-- EVOLVE-BLOCK-END\n"
)


def test_feedback_complete_proof() -> None:
    feedback = format_check_feedback(CompileResult(diagnostics=(), has_sorry=False))
    assert "proof is complete" in feedback.lower()


def test_feedback_compiles_with_sorry() -> None:
    result = CompileResult(
        diagnostics=(Diagnostic("warning", "declaration uses `sorry`"),),
        has_sorry=True,
    )
    feedback = format_check_feedback(result)
    assert "still contains" in feedback


def test_feedback_compile_error() -> None:
    result = CompileResult(diagnostics=(Diagnostic("error", "boom", 3),))
    feedback = format_check_feedback(result)
    assert "boom" in feedback
    assert "proof is complete" not in feedback.lower()


def test_feedback_system_error() -> None:
    feedback = format_check_feedback(CompileResult(system_error="sandbox died"))
    assert "sandbox died" in feedback


def test_render_basic_prompt() -> None:
    rendered = render_basic_prompt(SAMPLE, "/tmp/apn_proof.lean")
    assert "world-class mathematician" in rendered
    assert "theorem tgt : True" in rendered
    assert "/tmp/apn_proof.lean" in rendered
    assert "{code}" not in rendered
    assert "{path}" not in rendered
    assert "text_editor" in rendered
    assert "EVOLVE-BLOCK-START" in rendered
