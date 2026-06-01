"""Tests for the lean_check feedback formatting and the basic-agent prompt."""

from __future__ import annotations

from apn.prompts import LEAN_INSTRUCTIONS, render_task
from apn.tools import format_check_feedback
from apn.verifier.base import CompileResult, Diagnostic


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


def test_render_task_references_path() -> None:
    rendered = render_task("/tmp/apn_proof.lean")
    assert "/tmp/apn_proof.lean" in rendered
    assert "lean_check" in rendered


def test_instructions_cover_rules() -> None:
    assert "Lean 4" in LEAN_INSTRUCTIONS
    assert "lean_check" in LEAN_INSTRUCTIONS
    assert "statement" in LEAN_INSTRUCTIONS
