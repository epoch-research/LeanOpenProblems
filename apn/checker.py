"""Final proof checking via SafeVerify.

The authoritative anti-cheat is the vendored ``safe_verify`` executable
(see ``apn/lean/safeverify/``): given two ``.olean`` files it re-checks the
submission against the target spec at the kernel level (same name/kind/type for
every target declaration, ``sorry``-free, only the standard axioms). Its raw
interface is::

    lake env lean -o target.olean target.lean        # compile the spec
    lake env lean -o submission.olean submission.lean
    lake env safe_verify --disproofs target.olean submission.olean  # exit 0 = accepted

``--disproofs`` lets the agent *resolve* a conjecture either way: a target
theorem ``foo`` is accepted by a proof of ``foo`` itself, **or** by a separate
``foo.disproof`` whose type SafeVerify checks is the negation of ``foo``'s
statement (kernel ``isDefEq`` against its negation-normal-form). The "or" lives
inside ``safe_verify``, so this module's verdict mapping is unchanged.

This module drives those commands in the trusted scorer sandbox, one
``sandbox().exec`` per step, and maps the result to a verdict. The governing
rule is *whose code failed*:

* **Reference side** -- compiling the trusted, fixed target spec. If that fails
  for any reason (nonzero exit, OOM/signal kill, timeout) it is *our* bug, no
  verdict is possible -> raise, so the sample errors out and is rerun/inspected.
* **Agent side** -- compiling the submission, and ``safe_verify`` replaying it.
  Any failure here is a verdict on the agent's code, never an infra raise:
    - submission won't compile -> ``stage="compile_submission"``;
    - ``safe_verify`` exit 0 -> accepted; plain nonzero -> ``stage="safeverify"``;
    - OOM / signal kill (exit >= 128) -> ``stage="*_resource"``;
    - timeout (provider raises ``TimeoutError``) -> ``stage="*_timeout"``;
    - undecodable output (provider raises ``UnicodeDecodeError``) ->
      ``stage="*_decode"``.

Why agent-side resource deaths are a verdict, not a raise: an OOM or timeout
here is almost always the agent's expensive proof term, not our infrastructure.
safe_verify's memory/time use on a submission can vastly exceed the agent-side
compile cost (its un-memoized rebuildExpr expands pointer-shared proof terms,
e.g. from ``ring``, exponentially). These failures are *deterministic* per
submission, so raising-and-rerunning can never resolve them -- it just discards
the sample. Telling the agent its submission could not be verified lets it
produce a cheaper proof. See the scorer mem_limit comment in apn/task.py for
measurements. (The reference target spec is small and fixed, so it does not hit
these limits; if it ever did, that is genuinely our problem -> raise.)
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol, runtime_checkable

from inspect_ai.util import sandbox

# Paths inside the scorer image (the scorer stage of apn/lean/Dockerfile). The Lean
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

    def __init__(
        self,
        sandbox_name: str | None = None,
        timeout: int = 900,
        allow_disproofs: bool = True,
    ) -> None:
        self._sandbox_name = sandbox_name
        self._timeout = timeout
        # When set, pass ``--disproofs`` so a submission may *disprove* a target
        # theorem ``foo`` by supplying ``foo.disproof`` whose type is SafeVerify's
        # negation-normal-form of ``foo``'s statement (``∀`` -> ``∃¬``, ``∧`` ->
        # ``→¬``, ``≠`` -> ``=``, ...), proved sorry-free with the standard
        # axioms. SafeVerify checks that negation by kernel ``isDefEq`` and
        # accepts ``foo`` *or* ``foo.disproof`` for the target; the definitions
        # and test lemmas must still be reproduced and proved either way.
        self._allow_disproofs = allow_disproofs

    async def _exec_reference(self, cmd: list[str]) -> tuple[int, str]:
        """Run a *reference-side* step (workspace cleanup, target compile).

        Any failure is our infrastructure: a signal kill (exit >= 128) raises,
        and a ``TimeoutError`` / ``UnicodeDecodeError`` from the provider is left
        to propagate. The caller turns a nonzero exit into a raise too.
        """
        result = await sandbox(self._sandbox_name).exec(
            cmd, cwd=PROJECT, timeout=self._timeout
        )
        output = (result.stdout + "\n" + result.stderr).strip()
        if result.returncode >= 128:
            raise RuntimeError(
                f"Reference SafeVerify step {cmd[:3]} was killed "
                f"(exit {result.returncode}). Output tail:\n{output}"
            )
        return result.returncode, output

    async def _exec_submission(self, cmd: list[str]) -> tuple[str, str]:
        """Run an *agent-side* step (submission compile, safe_verify replay).

        Returns ``(mode, output)`` where ``mode`` is one of ``"ok"`` (exit 0),
        ``"exit"`` (plain nonzero), ``"resource"`` (signal kill, e.g. 137 OOM),
        ``"timeout"``, or ``"decode"``. Failures map to a verdict, never a raise:
        a timeout and an undecodable byte are *raised* by the sandbox provider
        (so they are caught here at the ``.exec()`` call), while an OOM comes
        back as a returned exit code >= 128.
        """
        try:
            result = await sandbox(self._sandbox_name).exec(
                cmd, cwd=PROJECT, timeout=self._timeout
            )
        except TimeoutError as exc:
            return "timeout", str(exc)
        except UnicodeDecodeError as exc:
            return "decode", str(exc)
        output = (result.stdout + "\n" + result.stderr).strip()
        if result.returncode >= 128:
            return "resource", f"killed (exit {result.returncode})\n{output}"
        if result.returncode != 0:
            return "exit", output
        return "ok", output

    async def check(self, target: str, submission: str) -> CheckOutcome:
        sb = sandbox(self._sandbox_name)
        # Clear any artifacts from a previous call (.olean/.ilean/.lean, plus
        # whatever lake leaves behind) before staging this one, so a crashed
        # prior call can't bleed a stale submission.olean into this verdict.
        await self._exec_reference(["rm", "-rf", SCORE_DIR])
        files = {"target": target, "submission": submission}
        for stem, source in files.items():
            await sb.write_file(f"{SCORE_DIR}/{stem}.lean", source)

        # The target spec is trusted, fixed data: if it fails to compile -- or
        # dies to a signal/timeout -- that is our problem, not the agent's, so
        # _exec_reference raises (a timeout propagates as TimeoutError).
        returncode, output = await self._exec_reference(
            ["lake", "env", "lean", "-o", f"{SCORE_DIR}/target.olean", f"{SCORE_DIR}/target.lean"]
        )
        if returncode != 0:
            raise RuntimeError(f"target spec failed to compile:\n{output}")

        # Everything below operates on the agent's submission: a failure is a
        # verdict on the agent's code, reported back, never an errored sample.
        mode, output = await self._exec_submission(
            ["lake", "env", "lean", "-o", f"{SCORE_DIR}/submission.olean", f"{SCORE_DIR}/submission.lean"]
        )
        if mode in ("resource", "timeout", "decode"):
            return CheckOutcome(ok=False, stage=f"compile_submission_{mode}", detail=output)
        if mode != "ok":
            return CheckOutcome(ok=False, stage="compile_submission", detail=output)

        # safe_verify exits 0 only on the verification-passed path; a plain
        # nonzero exit means it ran and rejected (a plain check failure or a
        # replay-time rejection: unsafe/partial constant, kernel type-check
        # failure, missing imports, ...). An OOM/timeout/decode death here is
        # the agent's expensive proof term -- also a rejection, not a raise.
        safe_verify_cmd = ["lake", "env", SAFE_VERIFY_BIN]
        if self._allow_disproofs:
            safe_verify_cmd.append("--disproofs")
        safe_verify_cmd += [f"{SCORE_DIR}/target.olean", f"{SCORE_DIR}/submission.olean"]
        mode, output = await self._exec_submission(safe_verify_cmd)
        if mode in ("resource", "timeout", "decode"):
            return CheckOutcome(ok=False, stage=f"safeverify_{mode}", detail=output)
        return CheckOutcome(ok=mode == "ok", stage="safeverify", detail=output)
