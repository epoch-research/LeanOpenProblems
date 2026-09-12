from __future__ import annotations

import io
import json
import tarfile
from contextlib import asynccontextmanager
from dataclasses import dataclass
from pathlib import PurePosixPath
from typing import Literal, Protocol, runtime_checkable
from collections.abc import AsyncIterator

from inspect_ai.util import OutputLimitExceededError, SandboxEnvironment, sandbox

from apn.layout import ENTRY_MODULE, ENTRY_PATH, ENTRY_REL, PROJECT, SUBMISSION_DIR
from apn.sandbox import SandboxBackend, k8s_scoring_env

# Paths inside the trusted `comparator` sandbox (the comparator stage of
# apn/lean/Dockerfile). The challenge is staged into the lake project's `run/`
# scratch lib; the agent's submission tree is staged at `Submission/` -- the
# path it has in the agent's sandbox, registered as the `Submission` lean_lib
# in the image's lakefile.toml, so `Submission/Foo/Bar.lean` is the module
# `Submission.Foo.Bar` in both sandboxes and the scored module is the agent's
# own entry module. The comparator binary is invoked under `lake env` so
# builds/exports resolve against the prebuilt Mathlib + FormalConjectures
# oleans.
RUN_DIR = f"{PROJECT}/run"
CHALLENGE_PATH = f"{RUN_DIR}/Challenge.lean"
CONFIG_PATH = f"{RUN_DIR}/config.json"
# The sanitized submission archive (see sanitize_submission), unpacked into
# SUBMISSION_DIR.
SUBMISSION_TAR_PATH = f"{RUN_DIR}/submission.tar"

COMPARATOR_BIN = "/opt/apn/comparator/bin/comparator"
RESET_SCRIPT = "/opt/apn/reset-dotlake.sh"

# The non-privileged user scoring work in the comparator sandbox runs as
# (comparator README assumption 6). The image itself stays root -- Inspect's
# sandbox plumbing assumes the default user can write anywhere, and
# k8s_sandbox implements per-exec `user=` with runuser(1), root-only -- so the
# privilege drop rides on each exec call instead of a Dockerfile USER
# directive (see the comparator stage of apn/lean/Dockerfile). Only the
# comparator run drops: the .lake reset must out-privilege the build's traps,
# and the staging steps deliberately leave root-owned inputs (below).
COMPARATOR_USER = "comparator"

# The trusted staging commands, module-level so the unit tests can script the
# exact exec sequence. Both run as root, like write_file: the staging
# directories and everything in them are then root-owned and read-only to the
# untrusted build (which runs as COMPARATOR_USER), so the build can neither
# alter them mid-check nor leave a permission trap that obstructs the next
# check's rm -rf (Landlock does not govern chmod; only .lake, which the build
# owns, needs the root reset for that). tar(1) here parses only an archive
# this module built (sanitize_submission), never the agent's bytes.
STAGING_RESET_CMD = [
    "sh", "-c", f"rm -rf {RUN_DIR} {SUBMISSION_DIR} && mkdir {RUN_DIR} {SUBMISSION_DIR}",
]
UNPACK_CMD = [
    "tar", "--no-same-owner", "--no-same-permissions",
    "-xf", SUBMISSION_TAR_PATH, "-C", SUBMISSION_DIR,
]

# The axioms a solution's proof closure may use (comparator rejects everything
# else, `sorryAx` and `Lean.ofReduceBool` included). The agent prompt renders
# its axiom list from this tuple (apn.prompts), so the two cannot drift.
PERMITTED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")

# Cap on the total bytes of module content a submission may stage. The tar
# itself is already capped by the sandbox read (MAX_READ_FILE_SIZE, 100 MiB)
# and is uncompressed, so only sparse members can claim more than the tar's
# size -- adversarial by construction, so it is folded into the entry_missing
# verdict.
MAX_SUBMISSION_BYTES = 100 * 1024 * 1024

# Bounds on a staged path, relative to Submission/, in UTF-8 bytes as the
# kernel measures them: NAME_MAX per component, and a whole-path bound well
# under PATH_MAX with the staging prefix, so unpacking cannot fail on a name
# accepted here (which would surface as an infrastructure error, not a
# verdict).
MAX_COMPONENT_BYTES = 255
MAX_MODULE_PATH_BYTES = 1024

# The entry module's path relative to SUBMISSION_DIR (`Spec.lean`).
ENTRY_MEMBER = PurePosixPath(ENTRY_PATH).relative_to(SUBMISSION_DIR)

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


class InvalidSubmission(Exception):
    """The agent's ``Submission/`` tar cannot be staged as a submission.

    A verdict on the submission (it scores INCORRECT under the ``entry_missing``
    stage), never an infrastructure error: every cause is agent-controlled.
    """


def module_path(member_name: str) -> PurePosixPath | None:
    """The ``Submission/``-relative path a tar member is staged at, or ``None``
    if the member is not a stageable Lean module.

    Members are named relative to ``Submission/`` (``./Spec.lean``,
    ``Helpers/Aux.lean``; a leading ``./`` is dropped). Stageable means a
    relative ``.lean`` path that stays inside the tree (no ``..`` component),
    is valid UTF-8 without NUL, and fits the filesystem's name and path
    bounds. Nothing more: whether Lake can import the module under that name
    (``Submission.Helpers.Aux``; ``Submission.«my-helpers».Aux`` for a name
    that needs quoting) is Lake's call, made identically in the agent's
    sandbox and the checker's, so what builds for the agent builds for the
    verifier. Anything else -- notes, build output, backups -- is not part of
    the submission.
    """
    try:
        raw = member_name.encode("utf-8")
    except UnicodeEncodeError:
        # tarfile surrogate-escapes undecodable name bytes. No Lean module
        # name maps to such a file, so it is unimportable in both sandboxes.
        return None
    # A NUL would truncate the name at unpack time, so it must fail here, not
    # pass as a component that merely *contains* `..`.
    if b"\x00" in raw or len(raw) > MAX_MODULE_PATH_BYTES:
        return None
    # PurePosixPath collapses `.` components and repeated slashes; `..` stays
    # a component. A bare `.lean` has no suffix (a dotfile), so it fails too.
    path = PurePosixPath(member_name)
    if path.is_absolute() or not path.parts or path.suffix != ".lean":
        return None
    if any(
        part == ".." or len(part.encode("utf-8")) > MAX_COMPONENT_BYTES
        for part in path.parts
    ):
        return None
    return path


def sanitize_submission(submission_tar: bytes) -> bytes:
    """Re-serialize the agent's ``Submission/`` tar as a trusted archive of
    exactly its Lean modules.

    The input is untrusted: the scorer tars the agent's directory inside the
    agent's own sandbox, which the agent controls down to ``tar(1)`` itself,
    so the bytes may be anything. They are parsed here in Python
    (``tarfile``), never with ``tar(1)`` inside the trusted container. Of the
    members, only regular files at a :func:`module_path` are kept;
    directories, links, devices and non-``.lean`` files are dropped. Each
    kept member is re-emitted under its normalized name with
    fixed metadata (mode 0644, root-owned, epoch mtime) and its content
    verbatim -- opaque bytes, never decoded: Lean itself rejects a malformed
    source file, exactly as it would in the agent's sandbox. The result is a
    plain archive of regular files under validated relative names, which the
    checker unpacks with ``tar(1)`` in the comparator sandbox.

    Raises :class:`InvalidSubmission` (a verdict, not an error) when the input
    is not an uncompressed tar, two members normalize to the same path, the
    kept members' declared sizes exceed ``MAX_SUBMISSION_BYTES``, or there is
    no ``Spec.lean`` at the root.
    """
    out = io.BytesIO()
    staged: set[PurePosixPath] = set()
    total = 0
    try:
        # "r:" -- uncompressed only. Transparent decompression would let a
        # 100 MiB archive expand into gigabytes of headers before any
        # per-member check runs.
        with (
            tarfile.open(fileobj=io.BytesIO(submission_tar), mode="r:") as src,
            tarfile.open(fileobj=out, mode="w") as dst,
        ):
            for member in src.getmembers():
                if not member.isfile():
                    continue
                rel = module_path(member.name)
                if rel is None:
                    continue
                if rel in staged:
                    raise InvalidSubmission(f"submission tar names {rel} twice")
                # Declared (logical) size, checked before the read: a sparse
                # member's data expands to this.
                total += member.size
                if total > MAX_SUBMISSION_BYTES:
                    raise InvalidSubmission(
                        f"submission exceeds {MAX_SUBMISSION_BYTES} bytes of Lean modules"
                    )
                extracted = src.extractfile(member)
                if extracted is None:
                    raise InvalidSubmission(f"cannot read {rel} from submission tar")
                data = extracted.read()
                info = tarfile.TarInfo(str(rel))
                info.size = len(data)
                info.mode = 0o644
                info.mtime = 0
                dst.addfile(info, io.BytesIO(data))
                staged.add(rel)
    except (tarfile.TarError, ValueError) as exc:
        raise InvalidSubmission(f"malformed submission tar: {exc}") from exc
    if ENTRY_MEMBER not in staged:
        raise InvalidSubmission(f"submission has no {ENTRY_REL}")
    return out.getvalue()


def comparator_config(decl: str, claim: Claim) -> str:
    """The per-check comparator config (see its README).

    The challenge is the sample's committed spec verbatim; it states both the
    target theorem and its ``.disproof`` negation, and the claim selects which
    one this check verifies. The solution is the agent's entry module, built in
    place from the staged submission tree. Nothing else varies per claim.
    """
    target = decl if claim == "proof" else f"{decl}.disproof"
    return json.dumps(
        {
            "challenge_module": "Challenge",
            "solution_module": ENTRY_MODULE,
            "theorem_names": [target],
            "permitted_axioms": list(PERMITTED_AXIOMS),
        },
        indent=2,
    )


class SandboxComparator:
    """Runs Lean FRO's Comparator against the trusted ``comparator`` sandbox.

    Per check (comparator-migration-plan.md §3.2): reset the sandbox's
    ``.lake`` to the image's pristine tree, recreate the ``run/`` and
    ``Submission/`` staging directories, stage the sample's spec as
    ``run/Challenge.lean`` and the agent's submission -- sanitized host-side
    to exactly its Lean modules -- as the ``Submission/`` tree, and invoke the
    comparator binary under ``lake env`` with the agent's entry module as the
    solution.
    Comparator builds+exports the challenge first (trusted), then builds the
    solution inside a landrun (Landlock) sandbox -- Lake compiles the helper
    modules the entry imports as part of that build -- exports it, compares
    the statement closures, checks the axiom closure, and kernel-replays the
    whole solution export, helpers included. Exit 0 is the only accept.

    Reset and staging are separate trusted operations, so their failures raise
    and error the sample. Once Comparator starts, its challenge build, solution
    build, export, comparison, and replay are treated as one opaque phase:
    captured output is bounded and submission-controlled, so it cannot provide
    a trustworthy phase boundary. Exit 0 is the only accept; every nonzero exit
    and timeout is a verdict on the submission and scores INCORRECT. Committed
    challenge validity is established before evaluation, not inferred from a
    Comparator transcript at scoring time.
    """

    def __init__(
        self,
        sandbox_name: str | None = "comparator",
        timeout: int = 60 * 60,
        backend: SandboxBackend = "docker",
        scoring_values: str | None = None,
    ) -> None:
        self._sandbox_name = sandbox_name
        self._timeout = timeout
        self._backend = backend
        self._scoring_values = scoring_values
        if backend == "k8s" and scoring_values is None:
            raise ValueError(
                "the k8s backend needs a scoring_values path "
                "(apn.task.get_scoring_config)."
            )

    @asynccontextmanager
    async def _env(self) -> AsyncIterator[SandboxEnvironment]:
        """The comparator sandbox for one check.

        On docker the comparator is a long-lived service, resolved by name.

        On k8s the comparator is a Helm release of its own, installed as
        needed and uninstalled when the scoring is finished.
        """
        if self._backend == "docker":
            yield sandbox(self._sandbox_name)
        else:
            assert self._scoring_values is not None  # enforced in __init__
            async with k8s_scoring_env(self._scoring_values) as env:
                yield env

    async def check(
        self, spec: str, submission_tar: bytes, decl: str, claim: Claim
    ) -> CheckOutcome:
        # Host-side: re-serialize the agent's tar as a trusted archive of its
        # Lean modules (a verdict if that is impossible; the sandbox is never
        # touched).
        try:
            staged = sanitize_submission(submission_tar)
        except InvalidSubmission as exc:
            return CheckOutcome(ok=False, stage="entry_missing", detail=str(exc))

        async with self._env() as sb:
            return await self._check_inner(sb, spec, staged, decl, claim)

    async def _check_inner(
        self,
        sb: SandboxEnvironment,
        spec: str,
        staged: bytes,
        decl: str,
        claim: Claim,
    ) -> CheckOutcome:
        # Trusted filesystem reset (a reference step: failure raises). It
        # restores a pristine .lake -- the only path the untrusted build can
        # write under its landrun sandbox; it does not terminate processes a
        # prior check left behind (Inspect issue #5034).
        # Root, not COMPARATOR_USER: the rm must clear permission traps (e.g.
        # a chmod-000 dir) the build can leave in .lake; the script itself
        # drops back to the comparator user for the copy.
        reset = await sb.exec([RESET_SCRIPT], timeout=self._timeout)
        if reset.returncode != 0:
            raise RuntimeError(
                f".lake reset failed (exit {reset.returncode}):\n"
                f"{(reset.stdout + reset.stderr)[-2000:]}"
            )

        # Recreate the staging directories (also trusted: failure raises).
        # Neither is inside the landrun write grant, so anything in them is our
        # own prior staging; fresh directories keep each check's inputs exactly
        # what is written below. Root-owned, so the build cannot touch them.
        clear = await sb.exec(STAGING_RESET_CMD, timeout=self._timeout)
        if clear.returncode != 0:
            raise RuntimeError(
                f"staging reset failed (exit {clear.returncode}):\n"
                f"{(clear.stdout + clear.stderr)[-2000:]}"
            )

        # Stage the check's inputs. The challenge is the committed spec
        # verbatim -- nothing is composed at scoring time. write_file has no
        # user switch, so these land as the container's root user (0644,
        # readable by COMPARATOR_USER) inside the root-owned staging dirs.
        await sb.write_file(CHALLENGE_PATH, spec)
        await sb.write_file(SUBMISSION_TAR_PATH, staged)
        await sb.write_file(CONFIG_PATH, comparator_config(decl, claim))

        # Unpack the submission tree (trusted: failure raises). The archive is
        # ours -- regular files under validated relative names, built above --
        # so tar(1) parses trusted bytes only; extracted as root, the tree is
        # read-only to the build like the rest of the staging.
        unpack = await sb.exec(UNPACK_CMD, timeout=self._timeout)
        if unpack.returncode != 0:
            raise RuntimeError(
                f"submission unpack failed (exit {unpack.returncode}):\n"
                f"{(unpack.stdout + unpack.stderr)[-2000:]}"
            )

        try:
            # lean4export and landrun sit on PATH in the image; comparator's
            # default resolution finds them (its README's preferred setup).
            result = await sb.exec(
                ["lake", "env", COMPARATOR_BIN, CONFIG_PATH],
                cwd=PROJECT,
                user=COMPARATOR_USER,
                timeout=self._timeout,
            )
        except TimeoutError as exc:
            return CheckOutcome(ok=False, stage="comparator_timeout", detail=str(exc))
        except UnicodeDecodeError as exc:
            # Non-UTF-8 bytes in the output stream come from the submission's
            # build (comparator's own output is clean text).
            return CheckOutcome(ok=False, stage="comparator", detail=str(exc))
        except OutputLimitExceededError as exc:
            # Output volume is submission-controlled too (the trusted phases
            # print a handful of progress lines), so a stream past Inspect's
            # exec cap is a verdict, not an infra raise -- an elaboration-time
            # print loop must not error the sample and dodge the INCORRECT.
            return CheckOutcome(
                ok=False, stage="comparator_output_limit", detail=str(exc)
            )

        output = (result.stdout + "\n" + result.stderr).strip()
        if result.returncode == 0:
            return CheckOutcome(ok=True, stage="comparator", detail=output)

        if result.returncode >= 128:
            return CheckOutcome(
                ok=False,
                stage="comparator_resource",
                detail=f"killed (exit {result.returncode})\n{output}",
            )
        return CheckOutcome(ok=False, stage="comparator", detail=output)
