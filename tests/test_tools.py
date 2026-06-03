"""Tests for the agent's bash wrapper and prompt rendering."""

from __future__ import annotations

import pytest
from inspect_ai.util import ExecResult

import apn.tools as tools_mod
from apn.prompts import lean_instructions, render_task
from apn.tools import bash


def test_render_task_references_path() -> None:
    rendered = render_task("/tmp/apn_proof.lean")
    assert "/tmp/apn_proof.lean" in rendered


def test_instructions_mention_lean_and_pypantograph() -> None:
    instructions = lean_instructions(token_limit=None)
    assert "Lean 4" in instructions
    assert "pantograph" in instructions.lower()
    # Statement-integrity rule must still be present (it's the one substantive
    # constraint the agent gets from the prompt rather than from the verifier).
    assert "statement" in instructions


def test_instructions_token_budget_rendering() -> None:
    # With a configured limit, the budget is disclosed with thousands separators.
    assert "100,000,000 tokens" in lean_instructions(token_limit=100_000_000)
    # Without one, the budget sentence is omitted entirely.
    assert "tokens" not in lean_instructions(token_limit=None).split("Facts about")[1]


def _exec_result(returncode: int, stdout: str = "", stderr: str = "") -> ExecResult[str]:
    return ExecResult(
        success=returncode == 0, returncode=returncode, stdout=stdout, stderr=stderr
    )


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
