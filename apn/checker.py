"""Final proof checking via SafeVerify.

The authoritative anti-cheat is the vendored ``safe_verify`` executable
(see ``apn/lean/safeverify/``): given two ``.olean`` files it re-checks the
submission against the target spec at the kernel level (same name/kind/type for
every target declaration, ``sorry``-free, only the standard axioms). Its raw
interface is::

    lake env lean -o target.olean     Submission/Spec.lean   # compile the trusted spec
    tar -xf submission.tar -C Submission                      # unpack the agent's file
    lake env lean -o submission.olean Submission/Spec.lean    # compile the submission
    lake env safe_verify --disproofs --save out.json target.olean submission.olean

The submission is a **single** Lean module: the entry module
``Submission/Spec.lean`` (Lean module ``Submission.Spec``) holding the
conjecture's defs + target theorem and a complete proof. The scorer hands
``check`` the raw tar of the agent's ``Submission/`` directory (read from its
sandbox) and the checker unpacks it into its own sandbox -- nothing decodes the
archive in Python.

Both sides compile the **same** way -- a standalone ``lake env lean -o`` at the
entry path ``Submission/Spec.lean``, which gives each the module name
``Submission.Spec``. That shared module name is load-bearing for private-name
matching (see ``check``), and compiling the submission standalone is load-bearing
for *soundness*: ``safe_verify`` kernel-replays only the declarations of the
file it is given, trusting the constants of any *imported* module (they enter via
``importModules`` and are not re-checked -- see ``apn/lean/safeverify``'s
README). A single replayed module therefore has nowhere to hide a kernel-invalid
constant. The agent cannot split its proof across imported helper modules:
``Submission`` is not a registered Lake library and no helper olean is ever
built, so an ``import Submission.…`` simply fails to compile and the submission
is rejected. Auxiliary defs/lemmas must live in ``Spec.lean`` itself, where they
are replayed.

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

Known, accepted security holes (out of scope; tracked as one separate hardening
effort, not patched piecemeal here):

* **Root code execution.** Compiling/replaying the submission elaborates
  agent-authored Lean as root in the scorer sandbox, so ``#eval`` / ``initialize``
  / an ``IO`` macro can run arbitrary code and could overwrite the co-located
  ``target.olean`` or the ``safe_verify`` binary before verification.
* **Zip-Slip.** The submission tar is produced by ``tar`` in the *agent's*
  sandbox (agent-owned, root), so its member names are untrusted; a forged
  ``../...`` entry could escape ``SUBMISSION_DIR`` when unpacked here. We do not
  path-validate -- it requires the agent to tamper with its own ``tar``, and the
  root-exec hole above already subsumes it.

The real fix for both is a non-root, sandboxed build with a hash-pinned target.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Any, Protocol, runtime_checkable

from inspect_ai.util import sandbox

from apn.layout import (
    ENTRY_PATH,
    ENTRY_REL,
    PROJECT,
    SUBMISSION_DIR,
)

# Paths inside the scorer image (the scorer stage of apn/lean/Dockerfile). The Lean
# files live inside the lake project so `lake env lean -o` resolves imports
# against the prebuilt Mathlib + FormalConjectures oleans.
SCORE_DIR = f"{PROJECT}/_apn_score"
# The trusted target and the agent's submission each compile to their own olean
# here, under the score scratch dir -- not into the lake build tree. So neither
# compile clobbers the other, and clearing SCORE_DIR each call leaves no stale
# olean (in particular none that an `import Submission.…` could resolve against).
TARGET_OLEAN = f"{SCORE_DIR}/target.olean"
SUBMISSION_OLEAN = f"{SCORE_DIR}/submission.olean"
# Where the agent's submission tar is staged before being unpacked into
# SUBMISSION_DIR (also under SCORE_DIR, cleared each call).
SUBMISSION_TAR = f"{SCORE_DIR}/submission.tar"
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
    async def check(
        self, target: str, submission_tar: bytes
    ) -> CheckOutcome:
        """Check ``submission_tar`` proves the spec in ``target`` without cheating.

        ``submission_tar`` is the agent's ``Submission/`` directory as raw tar
        bytes (members relative to that root, e.g. ``./Spec.lean``), exactly as
        :func:`apn.filetree.read_submission_tar` produces it. The checker unpacks
        it into its own sandbox and compiles; the entry module ``Spec.lean`` must
        be present after unpacking.
        """
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

    async def check(
        self, target: str, submission_tar: bytes
    ) -> CheckOutcome:
        sb = sandbox(self._sandbox_name)
        # Clear every artifact from a previous call before staging this one: the
        # target/report/olean scratch dir and the agent's whole Submission/
        # source tree. Both the target and the submission compile standalone into
        # SCORE_DIR (never into the lake build tree), so clearing it leaves no
        # stale olean to bleed into this verdict. Then recreate the two dirs.
        await self._exec_reference(["rm", "-rf", SCORE_DIR, SUBMISSION_DIR])
        await self._exec_reference(["mkdir", "-p", SCORE_DIR, SUBMISSION_DIR])

        # The flip. Compile the trusted target spec *at the submission's entry
        # path* (Submission/Spec.lean) so Lean assigns it the same module name
        # (Submission.Spec) the submission gets -- the submission is compiled
        # from that same path just below. Lean derives a file's module name from
        # its path relative to the project root and bakes that name into every
        # private / compiler-generated declaration: a pattern-matching ``def a``
        # emits equational lemmas that mangle to ``_private.<module>.0.a.match_1.eq_1``
        # (and ``.splitter`` / ``._arg_pusher``). SafeVerify matches each target
        # declaration against the submission by *exact name*, so if the two
        # compiled under different module names those private lemmas could never
        # match and a faithful, sorry-free proof would be rejected as
        # "declaration not found". Compiling both at Submission/Spec.lean makes
        # the module name -- and thus every mangled private name -- identical.
        # Those private lemmas are a pure function of (module name, def) and do
        # not depend on the proof body, so the sorry-bodied target and the
        # real-proof submission produce byte-identical private names (verified
        # against the toolchain). SafeVerify reads the two oleans by path and
        # replays them into separate environments, so the shared module name
        # causes no collision. Do NOT compile either side at some other path:
        # that silently reintroduces the module-name mismatch.

        # The target spec is trusted, fixed data: if it fails to compile -- or
        # dies to a signal/timeout -- that is our problem, not the agent's, so
        # _exec_reference raises (a timeout propagates as TimeoutError).
        await sb.write_file(ENTRY_PATH, target)
        returncode, output = await self._exec_reference(
            ["lake", "env", "lean", "-o", TARGET_OLEAN, ENTRY_REL]
        )
        if returncode != 0:
            raise RuntimeError(f"target spec failed to compile:\n{output}")

        # Remove the target's entry file before unpacking the submission, so a
        # submission that omits Spec.lean can't masquerade behind the trusted
        # target text we just wrote there (we'd otherwise "verify" our own spec).
        await self._exec_reference(["rm", "-f", ENTRY_PATH])

        # Everything below operates on the agent's submission: a failure is a
        # verdict on the agent's code, reported back, never an errored sample.
        # Unpack the agent's tar straight into SUBMISSION_DIR (PortBench's
        # approach -- no Python file-by-file staging; `tar` recreates the helper
        # subdirs). The submission tar is agent-controlled and NOT path-validated:
        # a forged member named e.g. ``../_apn_score/target.olean`` would escape
        # SUBMISSION_DIR here (a Zip-Slip). This is a known, accepted hole --
        # subsumed by the root-code-exec hole noted in the module docstring and
        # tracked as separate hardening (see apn.scorer).
        await sb.write_file(SUBMISSION_TAR, submission_tar)
        mode, output = await self._exec_submission(
            ["tar", "-xf", SUBMISSION_TAR, "-C", SUBMISSION_DIR]
        )
        if mode != "ok":
            return CheckOutcome(ok=False, stage="compile_submission", detail=output)

        # The entry module must exist after unpacking -- without it there is
        # nothing to build at Submission.Spec. (A `test -f` exit 1 is a normal
        # negative, not a signal, so _exec_reference returns it rather than
        # raising.)
        returncode, _ = await self._exec_reference(["test", "-f", ENTRY_PATH])
        if returncode != 0:
            return CheckOutcome(
                ok=False,
                stage="compile_submission",
                detail=f"entry module missing: {ENTRY_REL} not in submission",
            )

        # Compile the submission standalone -- exactly how the target was
        # compiled above (same entry path -> same module name -> matching private
        # names). This compiles ONLY Submission/Spec.lean, so safe_verify
        # kernel-replays the whole submission. An `import Submission.…` for a
        # helper module the agent added does NOT resolve (no helper olean is ever
        # built and Submission is not a registered lean_lib), so it fails here as
        # a plain compile error -> rejected. This is the single-file invariant:
        # there is no imported, un-replayed module for a kernel-invalid constant
        # to hide in (see the module docstring).
        mode, output = await self._exec_submission(
            ["lake", "env", "lean", "-o", SUBMISSION_OLEAN, ENTRY_REL]
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
        # --verbose makes safe_verify print detailed type-information on a
        # mismatch (target vs submission constant info), which lands in the
        # rejection ``detail`` for offline diagnosis.
        safe_verify_cmd.append("--verbose")
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
