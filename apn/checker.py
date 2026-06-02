"""Final proof checking via SafeVerify.

The authoritative anti-cheat is the vendored ``safe_verify`` executable
(see ``apn/lean/safeverify/``): given two ``.olean`` files it re-checks the
submission against the target spec at the kernel level (same name/kind/type for
every target declaration, ``sorry``-free, only the standard axioms). Its raw
interface is::

    lake env lean -o target.olean target.lean        # compile the spec
    lake env lean -o submission.olean submission.lean
    lake env safe_verify target.olean submission.olean   # exit 0 = accepted

This module drives those commands in the trusted scorer sandbox, one
``sandbox().exec`` per step, and maps the exit codes to a verdict:

* target fails to compile -> the *spec* is broken: infrastructure error, raise;
* submission fails to compile -> rejection (``stage="compile_submission"``);
* ``safe_verify`` exit 0 -> accepted; nonzero -> rejection (``stage="safeverify"``);
* any step killed by a signal (exit >= 128, e.g. 137 = SIGKILL from the OOM
  killer) or timing out -> not a verdict: raise, so the sample errors out and
  is rerun/inspected rather than silently scoring a possibly valid proof as
  INCORRECT.

Note that an OOM here can be triggered by a perfectly legitimate proof:
safe_verify's memory use on a submission can vastly exceed the agent-side
compile cost (its un-memoized rebuildExpr expands pointer-shared proof terms,
e.g. from ``ring``, exponentially). See the scorer mem_limit comment in
apn/task.py for measurements; such failures are deterministic per submission.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol, runtime_checkable

from inspect_ai.util import sandbox

# Paths inside the scorer image (see apn/lean/Dockerfile.scorer). The Lean
# files live inside the lake project so `lake env lean -o` resolves imports.
PROJECT = "/workspace/leanproject"
SCORE_DIR = f"{PROJECT}/_apn_score"
SAFE_VERIFY_BIN = "/opt/apn/safeverify/.lake/build/bin/safe_verify"


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
    """Compiles target + submission and runs ``safe_verify`` in the sandbox."""

    def __init__(self, sandbox_name: str | None = None, timeout: int = 600) -> None:
        self._sandbox_name = sandbox_name
        self._timeout = timeout

    async def _exec(self, cmd: list[str]) -> tuple[int, str]:
        result = await sandbox(self._sandbox_name).exec(
            cmd, cwd=PROJECT, timeout=self._timeout
        )
        output = (result.stdout + "\n" + result.stderr).strip()
        # Exit >= 128 means the process died from a signal (128 + N) -- e.g.
        # 137 = SIGKILL from the OOM killer. That is not a verdict on the
        # proof; treat it as an infrastructure failure wherever it happens.
        if result.returncode >= 128:
            raise RuntimeError(
                f"SafeVerify step {cmd[:3]} was killed (exit {result.returncode}) "
                f"before returning a verdict. Output tail:\n{output}"
            )
        return result.returncode, output

    async def check(self, target: str, submission: str) -> CheckOutcome:
        sb = sandbox(self._sandbox_name)
        # Clear any artifacts from a previous call (.olean/.ilean/.lean, plus
        # whatever lake leaves behind) before staging this one, so a crashed
        # prior call can't bleed a stale submission.olean into this verdict.
        await self._exec(["rm", "-rf", SCORE_DIR])
        files = {"target": target, "submission": submission}
        for stem, source in files.items():
            await sb.write_file(f"{SCORE_DIR}/{stem}.lean", source)

        # The target spec is trusted, fixed data: if it fails to compile that
        # is our problem, not the agent's.
        returncode, output = await self._exec(
            ["lake", "env", "lean", "-o", f"{SCORE_DIR}/target.olean", f"{SCORE_DIR}/target.lean"]
        )
        if returncode != 0:
            raise RuntimeError(f"target spec failed to compile:\n{output}")

        returncode, output = await self._exec(
            ["lake", "env", "lean", "-o", f"{SCORE_DIR}/submission.olean", f"{SCORE_DIR}/submission.lean"]
        )
        if returncode != 0:
            return CheckOutcome(ok=False, stage="compile_submission", detail=output)

        # safe_verify exits 0 only on the verification-passed path; any other
        # exit means it ran and rejected (a plain check failure or a
        # replay-time rejection: unsafe/partial constant, kernel type-check
        # failure, missing imports, ...).
        returncode, output = await self._exec(
            ["lake", "env", SAFE_VERIFY_BIN, f"{SCORE_DIR}/target.olean", f"{SCORE_DIR}/submission.olean"]
        )
        return CheckOutcome(ok=returncode == 0, stage="safeverify", detail=output)
