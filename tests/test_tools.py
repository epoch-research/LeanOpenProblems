"""Tests for the agent's bash wrapper and prompt rendering."""

from __future__ import annotations

import pytest
from inspect_ai.util import ExecResult

import apn.tools as tools_mod
from apn.layout import ENTRY_PATH
from apn.prompts import user_prompt
from apn.tools import bash

# The solver passes the absolute entry-module path (Submission/Spec.lean).
PROOF_PATH = ENTRY_PATH


def test_user_prompt_references_path() -> None:
    rendered = user_prompt(PROOF_PATH, token_limit=None, literature=False)
    assert PROOF_PATH in rendered


def test_user_prompt_explains_single_file_layout() -> None:
    # The agent must know its proof is a single file (Submission/Spec.lean),
    # type-checked with `lake env lean`, and that an `import Submission.…` for a
    # helper module of its own will NOT resolve (the proof stays in one file).
    rendered = user_prompt(PROOF_PATH, token_limit=None, literature=False)
    assert "Submission/Spec.lean" in rendered
    assert "Submission.Spec" in rendered
    assert "lake env lean Submission/Spec.lean" in rendered
    assert "one file" in rendered
    assert "import Submission" in rendered
    assert "will not" in rendered  # "they will not compile"


def test_user_prompt_mentions_lean_and_pypantograph() -> None:
    rendered = user_prompt(PROOF_PATH, token_limit=None, literature=False)
    assert "Lean 4" in rendered
    assert "pantograph" in rendered.lower()
    # Statement-integrity rule must still be present (it's the one substantive
    # constraint the agent gets from the prompt rather than from the verifier).
    assert "statement" in rendered


def test_user_prompt_explains_disproof_convention() -> None:
    # The agent must know it can disprove, and how: the `foo.disproof` naming
    # convention and the literal `negateExpr` the verifier applies to the target.
    rendered = user_prompt(PROOF_PATH, token_limit=None, literature=False)
    assert "disprove" in rendered.lower()
    assert "foo.disproof" in rendered
    assert "negateExpr" in rendered


def test_user_prompt_mentions_prove_or_disprove() -> None:
    rendered = user_prompt(PROOF_PATH, token_limit=None, literature=False)
    assert "disproof" in rendered
    assert "Settle" in rendered


def test_user_prompt_token_budget_rendering() -> None:
    # With a configured limit, the budget is disclosed with thousands separators.
    assert "100,000,000 tokens" in user_prompt(
        PROOF_PATH, token_limit=100_000_000, literature=False
    )
    # Without one, the budget sentence is omitted entirely.
    facts = user_prompt(PROOF_PATH, token_limit=None, literature=False).split("Facts about")[1]
    assert "tokens" not in facts


def test_user_prompt_literature_note_gated() -> None:
    # The /corpus note is included only on literature runs, so a closed-book
    # agent (whose image has no /corpus) is never told about a corpus it lacks.
    assert "/corpus" not in user_prompt(PROOF_PATH, token_limit=None, literature=False)
    assert "/corpus" in user_prompt(PROOF_PATH, token_limit=None, literature=True)


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
