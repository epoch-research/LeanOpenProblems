
from __future__ import annotations

import io
import json
import tarfile
from dataclasses import dataclass
from pathlib import PurePosixPath
from typing import Literal, Protocol, runtime_checkable

from inspect_ai.util import sandbox

from apn.layout import ENTRY_REL, PROJECT

# Paths inside the trusted `comparator` sandbox (the comparator stage of
# apn/lean/Dockerfile). The challenge/solution pair is staged into the lake
# project's `run/` scratch libs (registered in the image's lakefile.toml), and
# the comparator binary is invoked under `lake env` so builds/exports resolve
# against the prebuilt Mathlib + FormalConjectures oleans.
RUN_DIR = f"{PROJECT}/run"
CHALLENGE_PATH = f"{RUN_DIR}/Challenge.lean"
SOLUTION_PATH = f"{RUN_DIR}/Solution.lean"
CONFIG_PATH = f"{RUN_DIR}/config.json"

COMPARATOR_BIN = "/opt/apn/comparator/bin/comparator"
LEAN4EXPORT_BIN = "/opt/apn/lean4export/bin/lean4export"
LANDRUN_BIN = "/usr/local/bin/landrun"
RESET_SCRIPT = "/opt/apn/reset-dotlake.sh"

# The axioms a solution's proof closure may use (comparator rejects everything
# else, `sorryAx` and `Lean.ofReduceBool` included). Mirrored in the prompt.
PERMITTED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")

# Comparator's own phase marker: `safeLakeBuild` prints "Building Solution"
# before the first byte of agent code runs. Output containing it means the
# trusted challenge build+export completed, so any later failure is
# attributable to the submission; a failure *without* it is ours (the
# challenge spec, the config, or the image) and raises instead of scoring.
_SOLUTION_PHASE_MARKER = "Building Solution"

# Cap on the extracted Spec.lean member. The submission tar itself is already
# capped by the sandbox read (MAX_READ_FILE_SIZE, 100 MiB) and tar is
# uncompressed, so only a sparse member can claim more than the tar's size --
# adversarial by construction, so it is folded into the entry_missing verdict.
MAX_ENTRY_BYTES = 100 * 1024 * 1024

Claim = Literal["proof", "disproof"]


@dataclass(frozen=True)
class CheckOutcome:
    """Result of checking a submitted proof against the target spec."""

    ok: bool
    stage: str
    detail: str


@runtime_checkable
class ProofChecker(Protocol):
    async def check(
        self, spec: str, submission_tar: bytes, decl: str, claim: Claim
    ) -> CheckOutcome:
        ...


def extract_entry(submission_tar: bytes) -> str | None:
    """The submission's ``Spec.lean`` text, extracted host-side.

    Exactly one member of the agent's ``Submission/`` tar is scored --
    ``Spec.lean`` at the archive root (the tar is created with ``-C
    Submission/ .``, so the member is named ``./Spec.lean`` or ``Spec.lean``).
    Extraction happens here in Python (``tarfile``), never with ``tar(1)``
    inside the trusted container: the throwaway compile container used to
    absorb the risk of untrusted archives, and this is what replaces it.
    Returns ``None`` for anything that does not yield the member: a malformed
    tar, a missing/duplicated member, an oversized (sparse) member, or
    non-UTF-8 contents.
    """
    try:
        with tarfile.open(fileobj=io.BytesIO(submission_tar)) as tf:
            hits = [
                m
                for m in tf.getmembers()
                # "./Spec.lean" and "Spec.lean" normalize alike ("." collapses).
                if m.isfile() and PurePosixPath(m.name) == PurePosixPath("Spec.lean")
            ]
            if len(hits) != 1 or hits[0].size > MAX_ENTRY_BYTES:
                return None
            extracted = tf.extractfile(hits[0])
            if extracted is None:
                return None
            return extracted.read().decode("utf-8")
    except (tarfile.TarError, UnicodeDecodeError, ValueError):
        return None


def comparator_config(decl: str, claim: Claim) -> str:
    """The per-check comparator config (see its README).

    The challenge is the sample's committed spec verbatim; it states both the
    target theorem and its ``.disproof`` negation, and the claim selects which
    one this check verifies. Nothing else varies per claim.
    """
    target = decl if claim == "proof" else f"{decl}.disproof"
    return json.dumps(
        {
            "challenge_module": "Challenge",
            "solution_module": "Solution",
            "theorem_names": [target],
            "permitted_axioms": list(PERMITTED_AXIOMS),
        },
        indent=2,
    )


class SandboxComparator:
    """Runs Lean FRO's Comparator against the trusted ``comparator`` sandbox.

    Per check (comparator-migration-plan.md §3.2): reset the sandbox's
    ``.lake`` to the image's pristine tree, recreate the ``run/`` staging
    directory, stage the sample's spec as ``run/Challenge.lean`` and the
    agent's ``Spec.lean`` as ``run/Solution.lean``, and invoke the comparator
    binary under ``lake env``.
    Comparator builds+exports the challenge first (trusted), then builds the
    solution inside a landrun (Landlock) sandbox, exports it, compares the
    statement closures, checks the axiom closure, and kernel-replays the whole
    solution export. Exit 0 is the only accept.

    Error attribution keeps SafeVerify's reference/submission split: failures
    before comparator prints "Building Solution" happened while only *our*
    inputs were in play (workspace reset, challenge build/export, config) and
    raise -- erroring the sample; failures after it are a verdict on the
    agent's submission and score INCORRECT. A timeout of the whole exec cannot
    be phase-attributed (the provider raises without output) and is charged to
    the submission: the challenge phase re-elaborates one committed spec
    against prebuilt oleans, minutes at most against a much larger budget.
    """

    def __init__(
        self,
        sandbox_name: str | None = "comparator",
        timeout: int = 60 * 60,
    ) -> None:
        self._sandbox_name = sandbox_name
        self._timeout = timeout

    async def check(
        self, spec: str, submission_tar: bytes, decl: str, claim: Claim
    ) -> CheckOutcome:
        sb = sandbox(self._sandbox_name)

        # Host-side: pull exactly Spec.lean out of the agent's tar.
        solution = extract_entry(submission_tar)
        if solution is None:
            return CheckOutcome(
                ok=False,
                stage="entry_missing",
                detail=f"submission tar does not contain a well-formed {ENTRY_REL}",
            )

        # Trusted filesystem reset (a reference step: failure raises). It
        # restores a pristine .lake -- the only path the untrusted build can
        # write under its landrun sandbox; it does not terminate processes a
        # prior check left behind (Inspect issue #5034).
        reset = await sb.exec([RESET_SCRIPT], timeout=self._timeout)
        if reset.returncode != 0:
            raise RuntimeError(
                f".lake reset failed (exit {reset.returncode}):\n"
                f"{(reset.stdout + reset.stderr)[-2000:]}"
            )

        # Recreate the staging directory (also trusted: failure raises). run/
        # is outside the landrun write grant, so anything in it is our own
        # prior staging; a fresh directory keeps each check's inputs exactly
        # the three files written below.
        clear = await sb.exec(
            ["sh", "-c", f"rm -rf {RUN_DIR} && mkdir {RUN_DIR}"],
            timeout=self._timeout,
        )
        if clear.returncode != 0:
            raise RuntimeError(
                f"staging reset failed (exit {clear.returncode}):\n"
                f"{(clear.stdout + clear.stderr)[-2000:]}"
            )

        # Stage the check's inputs. The challenge is the committed spec
        # verbatim -- nothing is composed at scoring time.
        await sb.write_file(CHALLENGE_PATH, spec)
        await sb.write_file(SOLUTION_PATH, solution)
        await sb.write_file(CONFIG_PATH, comparator_config(decl, claim))

        try:
            result = await sb.exec(
                ["lake", "env", COMPARATOR_BIN, CONFIG_PATH],
                cwd=PROJECT,
                env={
                    "COMPARATOR_LEAN4EXPORT": LEAN4EXPORT_BIN,
                    "COMPARATOR_LANDRUN": LANDRUN_BIN,
                },
                timeout=self._timeout,
            )
        except TimeoutError as exc:
            return CheckOutcome(ok=False, stage="comparator_timeout", detail=str(exc))
        except UnicodeDecodeError as exc:
            # Non-UTF-8 bytes in the output stream come from the submission's
            # build (comparator's own output is clean text).
            return CheckOutcome(ok=False, stage="comparator", detail=str(exc))

        output = (result.stdout + "\n" + result.stderr).strip()
        if result.returncode == 0:
            return CheckOutcome(ok=True, stage="comparator", detail=output)

        submission_phase = _SOLUTION_PHASE_MARKER in output
        if not submission_phase:
            # The challenge build/export (or the reset workspace/config) failed
            # before any agent code ran: our infrastructure, not a verdict.
            raise RuntimeError(
                f"comparator failed before the solution phase "
                f"(exit {result.returncode}):\n{output[-4000:]}"
            )
        if result.returncode >= 128:
            return CheckOutcome(
                ok=False,
                stage="comparator_resource",
                detail=f"killed (exit {result.returncode})\n{output}",
            )
        return CheckOutcome(ok=False, stage="comparator", detail=output)
