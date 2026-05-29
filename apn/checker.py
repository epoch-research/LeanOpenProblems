"""Final proof checking via SafeVerify.

The authoritative anti-cheat is the vendored ``safe_verify`` executable, run in
the sandbox: it re-checks the submission against the target spec at the kernel
level (same name/kind/type for every target declaration, ``sorry``-free, only the
standard axioms). This module is the host-side interface to it.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Protocol, runtime_checkable

from inspect_ai.util import sandbox


@dataclass(frozen=True)
class CheckOutcome:
    """Result of checking a submitted proof against the target spec."""

    ok: bool
    stage: str
    detail: str


@runtime_checkable
class SafeVerifyChecker(Protocol):
    async def check(self, target: str, submission: str) -> CheckOutcome:
        """Check ``submission`` proves the spec in ``target`` without cheating."""
        ...


class SandboxSafeVerify:
    """Runs the in-sandbox ``apn_safeverify.py`` (compile + ``safe_verify``)."""

    def __init__(
        self,
        sandbox_name: str | None = None,
        script: str = "/opt/apn/apn_safeverify.py",
        timeout: int = 600,
    ) -> None:
        self._sandbox_name = sandbox_name
        self._script = script
        self._timeout = timeout

    async def check(self, target: str, submission: str) -> CheckOutcome:
        result = await sandbox(self._sandbox_name).exec(
            ["python3", self._script],
            input=json.dumps({"target": target, "submission": submission}),
            timeout=self._timeout,
        )
        if not result.success:
            return CheckOutcome(
                ok=False,
                stage="exec",
                detail=result.stderr.strip()[-4000:] or "sandbox exec failed",
            )
        try:
            data = json.loads(result.stdout)
        except json.JSONDecodeError:
            return CheckOutcome(ok=False, stage="parse", detail=result.stdout[-4000:])
        return CheckOutcome(
            ok=bool(data.get("ok", False)),
            stage=str(data.get("stage", "")),
            detail=str(data.get("detail", "")),
        )
