"""Tests for the agent's bash wrapper and prompt rendering."""

from __future__ import annotations

import pytest
from inspect_ai.util import ExecResult

import apn.tools as tools_mod
from apn.layout import ENTRY_PATH
from apn.prompts import user_prompt
from apn.tools import bash, resources

# The solver passes the absolute entry-module path (Submission/Spec.lean).
PROOF_PATH = ENTRY_PATH


def test_user_prompt_references_path() -> None:
    rendered = user_prompt(PROOF_PATH, token_limit=None, literature=False)
    assert PROOF_PATH in rendered


def test_user_prompt_mentions_lean_and_pypantograph() -> None:
    rendered = user_prompt(PROOF_PATH, token_limit=None, literature=False)
    assert "Lean 4" in rendered
    assert "pantograph" in rendered.lower()
    # Statement-integrity rule must still be present (it's the one substantive
    # constraint the agent gets from the prompt rather than from the verifier).
    assert "statement" in rendered


def test_user_prompt_explains_disproof_convention() -> None:
    # The agent must know it can disprove, and how: the `foo.disproof` naming
    # convention and that the disproof type is `¬` of the verbatim statement
    # (the verifier kernel-checks it against `negateExpr`, which is now plain `¬`).
    rendered = user_prompt(PROOF_PATH, token_limit=None, literature=False)
    assert "disprove" in rendered.lower()
    assert "foo.disproof" in rendered
    assert "¬" in rendered


def test_user_prompt_mentions_prove_or_disprove() -> None:
    rendered = user_prompt(PROOF_PATH, token_limit=None, literature=False)
    assert "disproof" in rendered
    assert "Settle" in rendered


def test_user_prompt_does_not_state_time_budget() -> None:
    # Per the tool-only design: the time budget is discoverable via the
    # `resources` tool, never stated as a number in the prompt.
    rendered = user_prompt(PROOF_PATH, token_limit=1_000_000, literature=False)
    assert "36 hours" not in rendered
    assert "129,600" not in rendered
    assert "working time" not in rendered.lower()


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


class _FakeLimit:
    """Stand-in for inspect_ai.util.Limit with the three fields the tool reads."""

    def __init__(self, *, usage: float, limit: float | None) -> None:
        self.usage = usage
        self.limit = limit

    @property
    def remaining(self) -> float | None:
        if self.limit is None:
            return None
        return self.limit - self.usage


class _FakeSampleLimits:
    def __init__(
        self,
        *,
        working: _FakeLimit,
        token: _FakeLimit | None = None,
        cost: _FakeLimit | None = None,
    ) -> None:
        # Default to "no limit set" for the spend limits not under test.
        self.token = token or _FakeLimit(usage=0, limit=None)
        self.cost = cost or _FakeLimit(usage=0, limit=None)
        self.working = working


def test_format_duration_compact() -> None:
    assert tools_mod._format_duration(0) == "0s"
    assert tools_mod._format_duration(129_600) == "36h"  # 36h exactly, no m/s
    assert tools_mod._format_duration(45) == "45s"
    assert tools_mod._format_duration(3 * 3600 + 25 * 60) == "3h 25m"


_HEADER = "Reaching any of the limits ends the task."


async def test_resources_tool_lists_all_limits_with_header(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # All limits are always listed under the "any one ends the task" header. Here
    # a token-limited run (no cost limit): Token cost reads "(no limit set)".
    monkeypatch.setattr(
        tools_mod,
        "sample_limits",
        lambda: _FakeSampleLimits(
            token=_FakeLimit(usage=10_000, limit=1_000_000),
            working=_FakeLimit(usage=3600, limit=129_600),
        ),
    )
    output = await resources()()
    assert output == (
        f"{_HEADER}\n"
        "- Token cost: $0.00 used (no limit set)\n"
        "- Tokens: 10,000 used, 990,000 remaining (limit 1,000,000)\n"
        "- Time: 1h used, 35h remaining (limit 36h)"
    )


async def test_resources_tool_reports_cost_in_usd(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A cost-limited run (no token limit): Token cost shows USD, Tokens "(no limit set)".
    monkeypatch.setattr(
        tools_mod,
        "sample_limits",
        lambda: _FakeSampleLimits(
            cost=_FakeLimit(usage=1.5, limit=200.0),
            working=_FakeLimit(usage=3600, limit=259_200),
        ),
    )
    output = await resources()()
    assert output == (
        f"{_HEADER}\n"
        "- Token cost: $1.50 used, $198.50 remaining (limit $200.00)\n"
        "- Tokens: 0 used (no limit set)\n"
        "- Time: 1h used, 71h remaining (limit 72h)"
    )


async def test_resources_tool_handles_all_limits_unset(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # With nothing configured, every line reads "(no limit set)" -- the header
    # makes clear that an unset dimension simply doesn't bound the run.
    monkeypatch.setattr(
        tools_mod,
        "sample_limits",
        lambda: _FakeSampleLimits(
            token=_FakeLimit(usage=500, limit=None),
            working=_FakeLimit(usage=120, limit=None),
        ),
    )
    output = await resources()()
    assert output == (
        f"{_HEADER}\n"
        "- Token cost: $0.00 used (no limit set)\n"
        "- Tokens: 500 used (no limit set)\n"
        "- Time: 2m used (no limit set)"
    )
