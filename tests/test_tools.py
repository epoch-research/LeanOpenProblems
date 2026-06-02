"""Tests for the lean_check feedback formatting and the basic-agent prompt."""

from __future__ import annotations

import json

import pytest
from inspect_ai.util import ExecResult

import apn.tools as tools_mod
import apn.verifier.pantograph as pantograph_mod
from apn._exec_status import exit_status_note
from apn.prompts import LEAN_INSTRUCTIONS, render_task
from apn.tools import bash, format_check_feedback
from apn.verifier.base import CompileResult, Diagnostic
from apn.verifier.pantograph import PantographVerifier


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


def _exec_result(returncode: int, stdout: str = "", stderr: str = "") -> ExecResult[str]:
    return ExecResult(
        success=returncode == 0, returncode=returncode, stdout=stdout, stderr=stderr
    )


def test_exit_status_note_none_on_success() -> None:
    assert exit_status_note(_exec_result(0)) is None


def test_exit_status_note_reports_raw_returncode() -> None:
    # No signal decoding -- the model interprets 137/139/127/etc itself.
    for rc in (1, 127, 137, 139):
        note = exit_status_note(_exec_result(rc))
        assert note is not None
        assert f"status {rc}" in note


class _FakeExecSandbox:
    """A sandbox stub that returns a fixed ExecResult from ``exec``."""

    def __init__(self, result: ExecResult[str]) -> None:
        self._result = result

    async def exec(self, *args: object, **kwargs: object) -> ExecResult[str]:
        return self._result


async def test_bash_tool_wraps_streams_in_xml_on_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        tools_mod,
        "sandbox",
        lambda *a, **k: _FakeExecSandbox(
            _exec_result(127, stdout="partial\n", stderr="not found")
        ),
    )
    output = await bash()("missing-binary")
    assert isinstance(output, str)
    assert output == (
        "<stdout>partial\n</stdout>\n"
        "<stderr>not found</stderr>\n"
        "<returncode>127</returncode>"
    )


async def test_bash_tool_wraps_sigkill_in_xml(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        tools_mod,
        "sandbox",
        lambda *a, **k: _FakeExecSandbox(_exec_result(137)),
    )
    output = await bash()("hungry")
    assert isinstance(output, str)
    assert "<returncode>137</returncode>" in output
    assert "<stdout></stdout>" in output
    assert "<stderr></stderr>" in output


async def test_bash_tool_passes_through_normal_output(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        tools_mod,
        "sandbox",
        lambda *a, **k: _FakeExecSandbox(_exec_result(0, stdout="hello\n")),
    )
    output = await bash()("echo hello")
    assert isinstance(output, str)
    assert output == "hello\n"
    assert "<stdout>" not in output


async def test_verifier_compile_surfaces_raw_exit_code(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # 137 (SIGKILL/OOM) and 1 (generic) are both reported by raw exit code;
    # the model interprets which is which.
    for rc in (1, 137):
        monkeypatch.setattr(
            pantograph_mod,
            "sandbox",
            lambda *a, _rc=rc, **k: _FakeExecSandbox(_exec_result(_rc)),
        )
        result = await PantographVerifier().compile("theorem t : True := trivial")
        assert result.system_error is not None
        assert f"status {rc}" in result.system_error


async def test_verifier_compile_success_parses_response(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    response = json.dumps({"diagnostics": [], "has_sorry": False})
    monkeypatch.setattr(
        pantograph_mod,
        "sandbox",
        lambda *a, **k: _FakeExecSandbox(_exec_result(0, stdout=response)),
    )
    result = await PantographVerifier().compile("theorem t : True := trivial")
    assert result.system_error is None
    assert result.ok
    assert result.has_sorry is False
