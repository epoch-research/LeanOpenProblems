"""Final proof checking via SafeVerify.

The authoritative anti-cheat is the vendored ``safe_verify`` executable
(see ``apn/lean/safeverify/``): given two ``.olean`` files it re-checks the
submission against the target spec at the kernel level (same name/kind/type for
every target declaration, ``sorry``-free, only the standard axioms). Its raw
interface is::

    lake env lean -o target.olean     spec.lean      # compile the spec
    lake env lean -o submission.olean spec.lean      # same source path (see check)
    lake env safe_verify --disproofs --save out.json target.olean submission.olean

Both files compile from the *same* source path so Lean gives them the same
module name; this is load-bearing for private-name matching -- see ``check``.

``--disproofs`` lets the agent *resolve* a conjecture either way: a target
theorem ``foo`` is accepted by a proof of ``foo`` itself, **or** by a separate
``foo.disproof`` whose type SafeVerify checks is the negation of ``foo``'s
statement (kernel ``isDefEq`` against its negation-normal-form). The "or" lives
inside ``safe_verify``, so this module's verdict mapping is unchanged.

``--save`` dumps a per-declaration JSON report (kind, axioms, failure mode),
which this module reads back and attaches to the :class:`CheckOutcome` (and
thence the score metadata) for offline analysis.

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

import json
from dataclasses import dataclass
from typing import Any, Protocol, runtime_checkable

from inspect_ai.util import sandbox

# Paths inside the scorer image (the scorer stage of apn/lean/Dockerfile). The Lean
# files live inside the lake project so `lake env lean -o` resolves imports.
PROJECT = "/workspace/leanproject"
SCORE_DIR = f"{PROJECT}/_apn_score"
# The target and the submission both compile from this one source path, one
# after the other (see SandboxSafeVerify.check for why), to two distinct oleans.
SOURCE = f"{SCORE_DIR}/spec.lean"
TARGET_OLEAN = f"{SCORE_DIR}/target.olean"
SUBMISSION_OLEAN = f"{SCORE_DIR}/submission.olean"
REPORT_PATH = f"{SCORE_DIR}/outcome.json"
SAFE_VERIFY_BIN = "/opt/apn/safeverify/.lake/build/bin/safe_verify"


@dataclass(frozen=True)
class CheckOutcome:
    """Result of checking a submitted proof against the target spec."""

    ok: bool
    stage: str
    detail: str
    # safe_verify's ``--save`` JSON: one entry per target declaration, recording
    # the target/submission kind + axioms and the per-declaration failure mode
    # (``None`` on success). Present only when safe_verify actually ran and wrote
    # it (so ``None`` when the submission never compiled, or safe_verify died to
    # a resource limit before writing).
    report: list[dict[str, Any]] | None = None


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
        # must still be reproduced either way.
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

        # Compile the target and the submission from the *same* source path
        # (SOURCE), one after the other, so Lean assigns them the same module
        # name. Lean derives a file's module name from its path relative to the
        # project root and bakes that name into every private / compiler-
        # generated declaration: a pattern-matching ``def a`` emits equational
        # lemmas that mangle to ``_private.<module>.0.a.match_1.eq_1`` (and
        # ``.splitter`` / ``._arg_pusher``). SafeVerify matches each target
        # declaration against the submission by *exact name*, so if the two
        # files compiled under different module names (``...target...`` vs
        # ``...submission...``) those private lemmas could never match and a
        # faithful, sorry-free proof was rejected as "declaration not found".
        # Sharing the source path makes the module name -- and thus every
        # mangled private name -- identical, while ``-o`` still writes two
        # distinct oleans. Those private lemmas are a pure function of (module
        # name, def) and do not depend on the proof body, so the sorry-bodied
        # target and the real-proof submission produce byte-identical private
        # names (verified against the toolchain). SafeVerify reads the two
        # oleans by path and replays them into separate environments, so the
        # shared module name causes no collision. Do NOT split this back into
        # target.lean / submission.lean: that silently reintroduces the
        # mismatch.

        # The target spec is trusted, fixed data: if it fails to compile -- or
        # dies to a signal/timeout -- that is our problem, not the agent's, so
        # _exec_reference raises (a timeout propagates as TimeoutError).
        await sb.write_file(SOURCE, target)
        returncode, output = await self._exec_reference(
            ["lake", "env", "lean", "-o", TARGET_OLEAN, SOURCE]
        )
        if returncode != 0:
            raise RuntimeError(f"target spec failed to compile:\n{output}")

        # Everything below operates on the agent's submission: a failure is a
        # verdict on the agent's code, reported back, never an errored sample.
        # Overwrite the shared source with the submission so it compiles under
        # the same module name as the target above.
        await sb.write_file(SOURCE, submission)
        mode, output = await self._exec_submission(
            ["lake", "env", "lean", "-o", SUBMISSION_OLEAN, SOURCE]
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
        # --save makes safe_verify dump a per-declaration JSON report (kind,
        # axioms, failure mode), written whether it accepts or rejects.
        safe_verify_cmd += ["--save", REPORT_PATH]
        safe_verify_cmd += [TARGET_OLEAN, SUBMISSION_OLEAN]
        mode, output = await self._exec_submission(safe_verify_cmd)
        report = await self._read_report()
        if mode in ("resource", "timeout", "decode"):
            return CheckOutcome(
                ok=False, stage=f"safeverify_{mode}", detail=output, report=report
            )
        return CheckOutcome(
            ok=mode == "ok", stage="safeverify", detail=output, report=report
        )

    async def _read_report(self) -> list[dict[str, Any]] | None:
        """Best-effort read of safe_verify's ``--save`` JSON from the sandbox.

        safe_verify writes it whenever it runs (accept or reject), and ``check``
        clears ``SCORE_DIR`` up front, so a present file is always this call's.
        A missing or unparseable file is not an error -- it just means no report
        (e.g. safe_verify was OOM-killed before writing), so we return ``None``.
        """
        try:
            raw = await sandbox(self._sandbox_name).read_file(REPORT_PATH)
        except FileNotFoundError:
            return None
        try:
            parsed = json.loads(raw)
        except ValueError:
            return None
        return parsed if isinstance(parsed, list) else None
