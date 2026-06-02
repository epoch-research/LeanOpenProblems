"""Render sandbox ``ExecResult`` exit status for the agent.

The built-in Inspect bash tool returns only stdout/stderr -- it discards the
returncode, so a process that died for any reason (command-not-found, permission
denied, uncaught Python exception, segfault, SIGKILL from the cgroup OOM
killer, ...) reaches the agent as silent missing output.

Inspect's sandbox interface has no dedicated flag for any of these cases; the
only signal it surfaces is ``ExecResult.returncode``. The Docker integration
already raises ``TimeoutError`` for timeout-induced 124/137/143 (see
``inspect_ai/util/_sandbox/docker/docker.py``), so any non-zero code we receive
here is a real process failure worth telling the agent about.

We just report the raw exit code; the LLM can interpret what 137, 139, 127,
etc. mean. No special-case decoding for OOM or anything else.
"""

from __future__ import annotations

from inspect_ai.util import ExecResult


def exit_status_note(result: ExecResult[str]) -> str | None:
    """Return a short note for a non-zero exit, or ``None`` if exit 0."""
    if result.returncode == 0:
        return None
    return f"Process exited with status {result.returncode}."
