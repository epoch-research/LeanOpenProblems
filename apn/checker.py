
from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Any, Protocol, runtime_checkable

from inspect_ai.util import OutputLimitExceededError, sandbox

from apn.layout import (
    ENTRY_PATH,
    ENTRY_REL,
    PROJECT,
    SUBMISSION_DIR,
)

# Paths inside the sandbox images (the scorer stage of apn/lean/Dockerfile,
# shared by the `compile` and `scorer` sandboxes -- both use that image). The
# Lean files live inside the lake project so `lake env lean -o` resolves imports
# against the prebuilt Mathlib + FormalConjectures oleans.

# --- compile sandbox (UNTRUSTED) --------------------------------------------- #
# The agent's tar is unpacked into SUBMISSION_DIR (= PROJECT/Submission) and the
# entry module compiled standalone to this olean. Compiling elaborates the
# agent's Lean, so this is where any compile-time code execution is contained.
COMPILE_DIR = f"{PROJECT}/_apn_compile"
COMPILE_SUBMISSION_TAR = f"{COMPILE_DIR}/submission.tar"
COMPILE_SUBMISSION_OLEAN = f"{COMPILE_DIR}/submission.olean"

# --- scorer sandbox (TRUSTED) ------------------------------------------------ #
# The trusted target compiles to TARGET_OLEAN; the olean produced in the compile
# sandbox is copied in to SUBMISSION_OLEAN; safe_verify reads both and writes its
# report to REPORT_PATH. Both oleans live under the score scratch dir (cleared
# each call), not the lake build tree.
SCORE_DIR = f"{PROJECT}/_apn_score"
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
    # safe_verify's ``--save`` JSON. Present only when safe_verify actually ran.
    report: list[dict[str, Any]] | None = None


@runtime_checkable
class SafeVerifyChecker(Protocol):
    async def check(
        self, target: str, submission_tar: bytes
    ) -> CheckOutcome:
        ...


class SandboxSafeVerify:
    """Compiles the submission in an untrusted sandbox, then runs ``safe_verify``
    against the trusted target in a separate trusted sandbox."""

    def __init__(
        self,
        sandbox_name: str | None = None,
        compile_sandbox_name: str = "compile",
        timeout: int = 30*60,
        allow_disproofs: bool = True,
    ) -> None:
        # The TRUSTED verify sandbox (trusted-target compile + safe_verify). Kept
        # as ``sandbox_name`` for back-compat -- callers pass sandbox_name="scorer".
        self._sandbox_name = sandbox_name
        # The UNTRUSTED, throwaway sandbox where the submission is unpacked and
        # compiled to an olean. Compile-time agent code runs only here.
        self._compile_sandbox_name = compile_sandbox_name
        self._timeout = timeout
        self._allow_disproofs = allow_disproofs

    async def _exec_reference(
        self, cmd: list[str], sandbox_name: str | None
    ) -> tuple[int, str]:
        """Run a *reference-side* step (scratch bookkeeping, trusted-target compile).

        Any failure is our infrastructure: a signal kill (exit >= 128) raises,
        and a ``TimeoutError`` / ``UnicodeDecodeError`` from the provider is left
        to propagate. The caller turns a nonzero exit into a raise too.
        """
        result = await sandbox(sandbox_name).exec(
            cmd, cwd=PROJECT, timeout=self._timeout
        )
        output = (result.stdout + "\n" + result.stderr).strip()
        if result.returncode >= 128:
            raise RuntimeError(
                f"Reference SafeVerify step {cmd[:3]} was killed "
                f"(exit {result.returncode}). Output tail:\n{output}"
            )
        return result.returncode, output

    async def _exec_submission(
        self, cmd: list[str], sandbox_name: str | None
    ) -> tuple[str, str]:
        """Run an *agent-side* step (submission compile, safe_verify replay).

        Returns ``(mode, output)`` where ``mode`` is one of ``"ok"`` (exit 0),
        ``"exit"`` (plain nonzero), ``"resource"`` (signal kill, e.g. 137 OOM),
        ``"timeout"``, or ``"decode"``. Failures map to a verdict, never a raise:
        a timeout and an undecodable byte are *raised* by the sandbox provider
        (so they are caught here at the ``.exec()`` call), while an OOM comes
        back as a returned exit code >= 128.
        """
        try:
            result = await sandbox(sandbox_name).exec(
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

    async def check(
        self, target: str, submission_tar: bytes
    ) -> CheckOutcome:
        compile_sb = sandbox(self._compile_sandbox_name)
        verify_sb = sandbox(self._sandbox_name)

        # ============================ COMPILE PHASE ========================== #
        # Runs in the UNTRUSTED compile sandbox. Elaborating the agent's Lean can
        # execute arbitrary code (a compile-time `#eval`/`initialize`).

        # Clear prior artifacts, then recreate the dirs
        await self._exec_reference(
            ["rm", "-rf", COMPILE_DIR, SUBMISSION_DIR], self._compile_sandbox_name
        )
        await self._exec_reference(
            ["mkdir", "-p", COMPILE_DIR, SUBMISSION_DIR], self._compile_sandbox_name
        )

        # Unpack the agent's tar straight into SUBMISSION_DIR
        await compile_sb.write_file(COMPILE_SUBMISSION_TAR, submission_tar)
        mode, output = await self._exec_submission(
            ["tar", "-xf", COMPILE_SUBMISSION_TAR, "-C", SUBMISSION_DIR],
            self._compile_sandbox_name,
        )
        if mode != "ok":
            return CheckOutcome(ok=False, stage="compile_submission", detail=output)

        # The entry module must exist after unpacking
        returncode, _ = await self._exec_reference(
            ["test", "-f", ENTRY_PATH], self._compile_sandbox_name
        )
        if returncode != 0:
            return CheckOutcome(
                ok=False,
                stage="compile_submission",
                detail=f"entry module missing: {ENTRY_REL} not in submission",
            )

        # Compile the submission standalone to an olean.
        mode, output = await self._exec_submission(
            ["lake", "env", "lean", "-o", COMPILE_SUBMISSION_OLEAN, ENTRY_REL],
            self._compile_sandbox_name,
        )
        if mode in ("resource", "timeout", "decode"):
            return CheckOutcome(ok=False, stage=f"compile_submission_{mode}", detail=output)
        if mode != "ok":
            return CheckOutcome(ok=False, stage="compile_submission", detail=output)

        # Read the produced olean out of the compile sandbox.
        try:
            submission_olean = await compile_sb.read_file(
                COMPILE_SUBMISSION_OLEAN, text=False
            )
        except FileNotFoundError:
            return CheckOutcome(
                ok=False,
                stage="compile_submission",
                detail="submission compiled but produced no readable olean",
            )
        except OutputLimitExceededError as exc:
            # The compile succeeded but produced an olean too large to read out of
            # the sandbox (Inspect's MAX_READ_FILE_SIZE).
            return CheckOutcome(
                ok=False, stage="compile_submission_oversize", detail=str(exc)
            )

        # ============================ VERIFY PHASE =========================== #
        # Runs in the TRUSTED scorer sandbox. We compile the trusted target spec and run
        # safe_verify on the two oleans.
        #
        # Clear prior artifacts, then recreate the dirs.
        await self._exec_reference(
            ["rm", "-rf", SCORE_DIR, SUBMISSION_DIR], self._sandbox_name
        )
        await self._exec_reference(
            ["mkdir", "-p", SCORE_DIR, SUBMISSION_DIR], self._sandbox_name
        )

        # Compile the trusted target spec *at the submission's entry
        # path* (Submission/Spec.lean) so Lean assigns it the same module name
        # (Submission.Spec) the submission got. Lean derives a file's
        # module name from its path relative to the project root and bakes that
        # name into every private / compiler-generated declaration: a
        # pattern-matching ``def a`` emits equational lemmas that mangle to
        # ``_private.<module>.0.a.match_1.eq_1`` (and ``.splitter`` /
        # ``._arg_pusher``). SafeVerify matches each target declaration against the
        # submission by *exact name*, so if the two compiled under different module
        # names those private lemmas could never match and a faithful
        # proof would be rejected as "declaration not found". Compiling both at
        # Submission/Spec.lean makes the module name -- and thus every mangled
        # private name -- identical.
        # SafeVerify reads the two
        # oleans by path and replays them into separate environments, so the shared
        # module name causes no collision.

        await verify_sb.write_file(ENTRY_PATH, target)
        returncode, output = await self._exec_reference(
            ["lake", "env", "lean", "-o", TARGET_OLEAN, ENTRY_REL], self._sandbox_name
        )
        if returncode != 0:
            raise RuntimeError(f"target spec failed to compile:\n{output}")

        # Copy the submission olean (built in the compile sandbox) into the scorer.
        await verify_sb.write_file(SUBMISSION_OLEAN, submission_olean)

        # safe_verify exits 0 only on the verification-passed path
        safe_verify_cmd = ["lake", "env", SAFE_VERIFY_BIN]
        if self._allow_disproofs:
            safe_verify_cmd.append("--disproofs")
        safe_verify_cmd.append("--verbose")
        # --save makes safe_verify dump a per-declaration JSON report (kind,
        # axioms, failure mode), written whether it accepts or rejects.
        safe_verify_cmd += ["--save", REPORT_PATH]
        safe_verify_cmd += [TARGET_OLEAN, SUBMISSION_OLEAN]
        mode, output = await self._exec_submission(safe_verify_cmd, self._sandbox_name)
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
        A missing file is not an error -- it just means no report (e.g. safe_verify was OOM-killed
        before writing), so we return ``None``.
        """
        try:
            raw = await sandbox(self._sandbox_name).read_file(REPORT_PATH)
        except (FileNotFoundError, OutputLimitExceededError):
            return None
        try:
            parsed = json.loads(raw)
        except ValueError:
            return None
        return parsed if isinstance(parsed, list) else None
