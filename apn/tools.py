
from __future__ import annotations

from typing import Callable

from inspect_ai.tool import Tool, tool
from inspect_ai.util import Limit, sample_limits, sandbox


@tool(name="bash")
def bash(
    timeout: int | None = None,
    user: str | None = None,
    sandbox_name: str | None = None,
) -> Tool:

    async def execute(command: str) -> str:
        """
        Use this function to execute bash commands.

        Args:
          command: The bash command to execute.

        Returns:
          The output of the command.
        """
        result = await sandbox(sandbox_name).exec(
            cmd=["bash", "--login", "-c", command], timeout=timeout, user=user
        )
        if result.returncode == 0:
            # Mimic inspect_ai.tool.bash, which just concatenates
            # stderr and stdout.
            output = ""
            if result.stderr:
                output = f"{result.stderr}\n"
            return f"{output}{result.stdout}"
        return (
            f"<stdout>{result.stdout}</stdout>\n"
            f"<stderr>{result.stderr}</stderr>\n"
            f"<returncode>{result.returncode}</returncode>"
        )

    return execute


def _format_tokens(value: float) -> str:
    return f"{round(value):,}"


def _format_usd(value: float) -> str:
    return f"${value:,.2f}"


def _format_duration(seconds: float) -> str:
    """Render a number of seconds as a compact ``Xh Ym Zs`` string.

    Zero-valued leading units are dropped (so 129_600 -> ``"36h"``), and a flat
    ``"0s"`` is shown for zero.
    """
    total = round(seconds)
    hours, rem = divmod(total, 3600)
    minutes, secs = divmod(rem, 60)
    parts = []
    if hours:
        parts.append(f"{hours}h")
    if minutes:
        parts.append(f"{minutes}m")
    if secs or not parts:
        parts.append(f"{secs}s")
    return " ".join(parts)


def _resource_line(label: str, limit: Limit, fmt: Callable[[float], str]) -> str:
    used = fmt(limit.usage)
    if limit.limit is None:
        return f"- {label}: {used} used (no limit set)"
    # remaining is non-None whenever limit is non-None (Limit.remaining).
    assert limit.remaining is not None
    return (
        f"- {label}: {used} used, {fmt(limit.remaining)} remaining "
        f"(limit {fmt(limit.limit)})"
    )


@tool(name="resources")
def resources() -> Tool:
    """A tool that reports the agent's limits and how much of each remains."""

    async def execute() -> str:
        """Check your remaining limits (cost, tokens, time)."""
        limits = sample_limits()
        lines = [
            _resource_line("Token cost", limits.cost, _format_usd),
            _resource_line("Tokens", limits.token, _format_tokens),
            # We surface the *working*-time limit plainly as "Time".
            # The working-time vs. clock-time distinction is not relevant to an agent.
            _resource_line("Time", limits.working, _format_duration),
        ]
        header = f"Reaching any of the limits ends the task. "
        return "\n".join([header, *lines])

    return execute

