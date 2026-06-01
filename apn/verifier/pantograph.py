"""A :class:`LeanVerifier` backed by Lean + Mathlib + Pantograph in a sandbox.

This runs on the Inspect (host) side. It compiles Lean by shelling into the
sample's Docker sandbox and invoking the ``apn_lean.py client`` helper, which
relays the request to a warm PyPantograph daemon (see ``apn/lean/apn_lean.py``).
The heavy Mathlib import is paid once per sample when the daemon starts.

Build the images before use (``apn/lean/build.sh``). The :func:`apn.task.apn_oeis`
task wires up the Docker sandbox(es); the daemon is started lazily by the client
on the first compile.
"""

from __future__ import annotations

import json

from inspect_ai.util import SandboxEnvironment, sandbox

from apn.verifier.base import CompileResult, Diagnostic, Severity

CLIENT_CMD = ["python3", "/opt/apn/apn_lean.py", "client"]


def _as_severity(value: object) -> Severity:
    if value == "error":
        return "error"
    if value == "warning":
        return "warning"
    return "info"


class PantographVerifier:
    """Compiles Lean inside a sandbox via the ``apn_lean`` daemon.

    Args:
        sandbox_name: Name of the sandbox environment to use (``None`` selects
            the default sandbox).
        timeout: Per-call timeout in seconds for the sandbox ``exec``.
    """

    def __init__(self, sandbox_name: str | None = None, timeout: int = 600) -> None:
        self._sandbox_name = sandbox_name
        self._timeout = timeout

    def _env(self) -> SandboxEnvironment:
        return sandbox(self._sandbox_name)

    async def _call(self, request: dict[str, object]) -> dict[str, object] | None:
        """Send one request to the daemon; return the parsed JSON or ``None``.

        ``None`` signals a transport/system failure (the caller renders it as a
        system error rather than a clean compile result).
        """
        result = await self._env().exec(
            CLIENT_CMD,
            input=json.dumps(request, ensure_ascii=False),
            timeout=self._timeout,
        )
        if not result.success:
            return None
        try:
            parsed = json.loads(result.stdout)
        except json.JSONDecodeError:
            return None
        if not isinstance(parsed, dict):
            return None
        return parsed

    async def compile(self, code: str) -> CompileResult:
        response = await self._call({"op": "compile", "code": code})
        if response is None:
            return CompileResult(system_error="sandbox exec or daemon transport failed")
        system_error = response.get("system_error")
        if system_error is not None:
            return CompileResult(system_error=str(system_error))

        diagnostics: list[Diagnostic] = []
        raw_diagnostics = response.get("diagnostics", [])
        if isinstance(raw_diagnostics, list):
            for item in raw_diagnostics:
                if not isinstance(item, dict):
                    continue
                diagnostics.append(
                    Diagnostic(
                        severity=_as_severity(item.get("severity")),
                        message=str(item.get("message", "")),
                        start_line=_as_int(item.get("line")),
                        start_col=_as_int(item.get("column")),
                    )
                )
        return CompileResult(
            diagnostics=tuple(diagnostics),
            has_sorry=bool(response.get("has_sorry", False)),
        )


def _as_int(value: object) -> int | None:
    return value if isinstance(value, int) else None
