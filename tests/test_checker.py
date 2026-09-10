"""Tests for the Comparator checker's exec orchestration and the scorer wiring.

``SandboxComparator`` drives one trusted ``comparator`` sandbox. Per check it:
resets the workspace (a reference step), recreates the ``run/`` and
``Submission/`` staging directories, writes ``run/Challenge.lean`` (the sample
spec verbatim), ``run/submission.tar`` (the agent's ``Submission/`` tar,
sanitized host-side to exactly its Lean modules) and ``run/config.json``,
unpacks the tar into ``Submission/``, then runs the comparator binary under
``lake env`` with the agent's entry module ``Submission.Spec`` as the solution.
Exit 0 accepts. Attribution keys off comparator's exit code rather than its
bounded, submission-controlled output: once the comparator starts, every
nonzero exit is a verdict on the submission. Failures in the separate trusted
reset, staging and unpack operations still raise.

A fake sandbox scripts the exec/write sequence to verify that mapping. The
scorer tests use a stub checker and a fake workspace sandbox to verify the
``Submission/`` tar is collected, the declared claim is read from the store,
and both are handed to the checker.
"""

from __future__ import annotations

import gzip
import io
import json
import tarfile
from pathlib import Path, PurePosixPath
from types import SimpleNamespace
from typing import cast

import pytest
from inspect_ai.model import ModelName
from inspect_ai.scorer import CORRECT, INCORRECT, Score, Target
from inspect_ai.solver import TaskState
from inspect_ai.util import ExecResult, OutputLimitExceededError

import apn.checker as checker_mod
import apn.scorer as scorer_mod
from apn.checker import (
    CHALLENGE_PATH,
    COMPARATOR_USER,
    CONFIG_PATH,
    RESET_SCRIPT,
    STAGING_RESET_CMD,
    SUBMISSION_TAR_PATH,
    UNPACK_CMD,
    CheckOutcome,
    InvalidSubmission,
    ProofChecker,
    SandboxComparator,
    module_path,
    sanitize_submission,
)
from apn.scorer import CLAIM_STORE_KEY, proof_scorer

SPEC = "import Mathlib\ntheorem tgt : True := by sorry\ntheorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"


def _tar_of(files: dict[str, str | bytes]) -> bytes:
    """Pack ``{relative path: contents}`` into the tar the checker consumes
    (members relative to ``Submission/``, i.e. ``./Spec.lean``)."""
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w") as tf:
        for name, content in files.items():
            data = content.encode() if isinstance(content, str) else content
            info = tarfile.TarInfo(name)
            info.size = len(data)
            tf.addfile(info, io.BytesIO(data))
    return buf.getvalue()


def _tar_with_special_members(files: dict[str, str]) -> bytes:
    """``_tar_of(files)`` plus one member of every non-regular kind at a
    module-path name -- a directory, a symlink, a hardlink, a character device
    and a fifo -- as an adversarial ``tar(1)`` could emit them."""
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w") as tf:
        for name, content in files.items():
            data = content.encode()
            info = tarfile.TarInfo(name)
            info.size = len(data)
            tf.addfile(info, io.BytesIO(data))
        for name, kind in [
            ("./Helpers", tarfile.DIRTYPE),
            ("./Helpers/Link.lean", tarfile.SYMTYPE),
            ("./Helpers/Hard.lean", tarfile.LNKTYPE),
            ("./Helpers/Dev.lean", tarfile.CHRTYPE),
            ("./Helpers/Fifo.lean", tarfile.FIFOTYPE),
        ]:
            info = tarfile.TarInfo(name)
            info.type = kind
            if kind in (tarfile.SYMTYPE, tarfile.LNKTYPE):
                info.linkname = "/etc/passwd" if kind == tarfile.SYMTYPE else "Spec.lean"
            tf.addfile(info)
    return buf.getvalue()


def _members(sanitized: bytes) -> dict[str, bytes]:
    """``{member name: content}`` of a sanitized archive, asserting every member
    is a regular file with the fixed metadata the sanitizer stamps."""
    out: dict[str, bytes] = {}
    with tarfile.open(fileobj=io.BytesIO(sanitized), mode="r:") as tf:
        for m in tf.getmembers():
            assert m.isfile(), f"{m.name}: not a regular file"
            assert (m.mode, m.uid, m.gid, m.mtime) == (0o644, 0, 0, 0), m.name
            extracted = tf.extractfile(m)
            assert extracted is not None
            out[m.name] = extracted.read()
    return out


SUBMISSION_TAR = _tar_of({"./Spec.lean": "theorem tgt : True := trivial\n"})


class StubChecker:
    def __init__(self, ok: bool) -> None:
        self._ok = ok
        self.calls: list[tuple[str, bytes, str, str]] = []

    async def check(
        self, spec: str, submission_tar: bytes, decl: str, claim: str
    ) -> CheckOutcome:
        self.calls.append((spec, submission_tar, decl, claim))
        return CheckOutcome(ok=self._ok, stage="stub", detail="stub outcome")


class FakeStore:
    """Minimal stand-in for Inspect's per-sample ``store()``."""

    def __init__(self, initial: dict[str, object] | None = None) -> None:
        self._data: dict[str, object] = dict(initial or {})

    def get(self, key: str, default: object = None) -> object:
        return self._data.get(key, default)

    def set(self, key: str, value: object) -> None:
        self._data[key] = value


class FakeSandbox:
    """Stands in for the agent's workspace sandbox: serves a fixed Submission tar.

    ``read_submission_tar`` runs ``tar``/``rm`` execs and reads the tar back, so
    this records execs and returns the scripted tar bytes from ``read_file``.
    """

    def __init__(self, tar: bytes) -> None:
        self._tar = tar
        self.execs: list[list[str]] = []

    async def exec(self, cmd: list[str], **kwargs: object) -> ExecResult[str]:
        self.execs.append(cmd)
        return ExecResult(success=True, returncode=0, stdout="", stderr="")

    async def read_file(self, file: str, text: bool = True) -> bytes:
        return self._tar


# --------------------------------------------------------------------------- #
# module_path: which tar members are Lean modules of the submission            #
# --------------------------------------------------------------------------- #
@pytest.mark.parametrize(
    ("name", "expected"),
    [
        # The entry, with and without tar's leading ./
        ("./Spec.lean", "Spec.lean"),
        ("Spec.lean", "Spec.lean"),
        # Helpers at any depth; digits and underscores allowed anywhere.
        ("./Helpers/Aux.lean", "Helpers/Aux.lean"),
        ("Helpers/Deep/Base_2.lean", "Helpers/Deep/Base_2.lean"),
        ("./a/./b.lean", "a/b.lean"),
        # A nested Spec.lean is an ordinary helper module, not the entry.
        ("Sub/Spec.lean", "Sub/Spec.lean"),
    ],
)
def test_module_path_accepts_module_files(name: str, expected: str) -> None:
    assert module_path(name) == PurePosixPath(expected)


@pytest.mark.parametrize(
    "name",
    [
        # Not .lean (case-sensitive), or a backup/double extension.
        "notes.md",
        "Spec.LEAN",
        "Spec.lean.bak",
        "Helpers/aux.olean",
        # Directory-ish names carry no file.
        "./Helpers/",
        ".",
        "",
        # Components outside the policy: hyphen, dot (hidden), space, quotes.
        "my-helpers/Aux.lean",
        ".hidden/Aux.lean",
        "Helpers/.Aux.lean",
        "Helpers/A.B.lean",
        "Helpers/A B.lean",
        "«weird».lean",
        # Escapes: traversal and absolute paths.
        "../Evil.lean",
        "Helpers/../../Evil.lean",
        "/workspace/leanproject/Submission/Spec.lean",
        # A component over NAME_MAX, and a path over the cap.
        "x" * 256 + ".lean",
        "/".join(["d"] * 600) + "/f.lean",
    ],
)
def test_module_path_rejects_non_modules(name: str) -> None:
    assert module_path(name) is None


# --------------------------------------------------------------------------- #
# sanitize_submission (host-side tar handling)                                 #
# --------------------------------------------------------------------------- #
def test_sanitize_keeps_entry_and_helpers_under_normalized_names() -> None:
    tar = _tar_of({
        "./Spec.lean": "the spec",
        "./Helpers/Aux.lean": "aux",
        "Helpers/Deep/Base.lean": "base",
    })
    assert _members(sanitize_submission(tar)) == {
        "Spec.lean": b"the spec",
        "Helpers/Aux.lean": b"aux",
        "Helpers/Deep/Base.lean": b"base",
    }


def test_sanitize_drops_non_module_files_and_special_members() -> None:
    # Notes, backups, files at names outside the module-path policy, and every
    # non-regular member kind are dropped; only the modules remain.
    tar = _tar_with_special_members({
        "./Spec.lean": "the spec",
        "./notes.md": "scratch",
        "./Spec.lean.bak": "old",
        "./old-attempts/try1.lean": "hyphenated dir",
        "./.lake/build/x.lean": "hidden dir",
    })
    assert _members(sanitize_submission(tar)) == {"Spec.lean": b"the spec"}


def test_sanitize_passes_content_bytes_verbatim() -> None:
    # Content is never decoded: a non-UTF-8 module is staged as is (Lean
    # rejects it at build time, exactly as in the agent's sandbox).
    raw = b"\xff\xfe not utf8"
    tar = _tar_of({"./Spec.lean": "ok", "./Helpers/Bad.lean": raw})
    assert _members(sanitize_submission(tar))["Helpers/Bad.lean"] == raw


def test_sanitize_requires_root_spec() -> None:
    with pytest.raises(InvalidSubmission, match="no Submission/Spec.lean"):
        sanitize_submission(_tar_of({"./Other.lean": "x"}))
    with pytest.raises(InvalidSubmission, match="no Submission/Spec.lean"):
        sanitize_submission(_tar_of({}))
    # A nested Spec.lean is a helper, not the entry.
    with pytest.raises(InvalidSubmission, match="no Submission/Spec.lean"):
        sanitize_submission(_tar_of({"./Sub/Spec.lean": "x"}))
    # A directory member named Spec.lean is not the entry either.
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w") as tf:
        info = tarfile.TarInfo("./Spec.lean")
        info.type = tarfile.DIRTYPE
        tf.addfile(info)
    with pytest.raises(InvalidSubmission, match="no Submission/Spec.lean"):
        sanitize_submission(buf.getvalue())


def test_sanitize_rejects_malformed_tar() -> None:
    with pytest.raises(InvalidSubmission, match="malformed"):
        sanitize_submission(b"not a tar at all")


def test_sanitize_rejects_compressed_tar() -> None:
    # Only an uncompressed archive is parsed (no transparent decompression):
    # the agent controls tar(1) in its sandbox, so a gzip bomb is a possible
    # input.
    compressed = gzip.compress(_tar_of({"./Spec.lean": "x"}))
    with pytest.raises(InvalidSubmission, match="malformed"):
        sanitize_submission(compressed)


def test_sanitize_rejects_duplicate_paths() -> None:
    # tar(1) over a directory never emits a path twice; a crafted archive can.
    with pytest.raises(InvalidSubmission, match="twice"):
        sanitize_submission(_tar_of({"./Spec.lean": "a", "Spec.lean": "b"}))


def test_sanitize_caps_total_module_bytes(monkeypatch: pytest.MonkeyPatch) -> None:
    # The cap is on the declared sizes of the *kept* members, checked before
    # any content is read. Shrink it so the fixtures stay small.
    monkeypatch.setattr(checker_mod, "MAX_SUBMISSION_BYTES", 8)
    with pytest.raises(InvalidSubmission, match="exceeds"):
        sanitize_submission(_tar_of({"./Spec.lean": "x" * 32}))
    with pytest.raises(InvalidSubmission, match="exceeds"):
        sanitize_submission(_tar_of({"./Spec.lean": "1234", "./Aux.lean": "56789"}))
    # Under the cap, and dropped members do not count toward it.
    tar = _tar_of({"./Spec.lean": "1234", "./Aux.lean": "5678", "./notes.md": "x" * 100})
    assert set(_members(sanitize_submission(tar))) == {"Spec.lean", "Aux.lean"}


# --------------------------------------------------------------------------- #
# SandboxComparator exec orchestration                                         #
# --------------------------------------------------------------------------- #
class ScriptedSandbox:
    """A stub for the comparator sandbox: records writes/execs (in one event
    stream, so their interleaving can be asserted) and returns (or raises) a
    scripted result for the .lake reset exec, the staging reset exec, the
    unpack exec, then the comparator exec."""

    def __init__(
        self,
        reset: ExecResult[str] | None = None,
        staging: ExecResult[str] | None = None,
        unpack: ExecResult[str] | None = None,
        comparator: ExecResult[str] | BaseException | None = None,
    ) -> None:
        self._reset = reset if reset is not None else ExecResult(True, 0, "", "")
        self._staging = staging if staging is not None else ExecResult(True, 0, "", "")
        self._unpack = unpack if unpack is not None else ExecResult(True, 0, "", "")
        self._comparator = comparator
        self.written: dict[str, object] = {}
        self.commands: list[list[str]] = []
        self.exec_kwargs: list[dict[str, object]] = []
        self.events: list[tuple[str, object]] = []

    async def write_file(self, file: str, contents: object) -> None:
        self.written[file] = contents
        self.events.append(("write", file))

    async def exec(self, cmd: list[str], **kwargs: object) -> ExecResult[str]:
        self.commands.append(cmd)
        self.exec_kwargs.append(kwargs)
        self.events.append(("exec", cmd))
        if cmd == [RESET_SCRIPT]:
            return self._reset
        if cmd == STAGING_RESET_CMD:
            return self._staging
        if cmd == UNPACK_CMD:
            return self._unpack
        step = self._comparator
        if isinstance(step, BaseException):
            raise step
        assert step is not None, f"unexpected exec: {cmd}"
        return step


def _ok(stdout: str = "", stderr: str = "") -> ExecResult[str]:
    return ExecResult(success=True, returncode=0, stdout=stdout, stderr=stderr)


def _fail(returncode: int, stdout: str = "", stderr: str = "") -> ExecResult[str]:
    return ExecResult(success=False, returncode=returncode, stdout=stdout, stderr=stderr)


_ACCEPT_OUT = "Building Challenge\nBuilding Submission.Spec\nYour solution is okay!"
COMPARATOR_CMD = ["lake", "env", checker_mod.COMPARATOR_BIN, CONFIG_PATH]


def _checker(
    monkeypatch: pytest.MonkeyPatch,
    reset: ExecResult[str] | None = None,
    staging: ExecResult[str] | None = None,
    unpack: ExecResult[str] | None = None,
    comparator: ExecResult[str] | BaseException | None = None,
) -> tuple[SandboxComparator, ScriptedSandbox]:
    sb = ScriptedSandbox(reset=reset, staging=staging, unpack=unpack, comparator=comparator)
    monkeypatch.setattr(checker_mod, "sandbox", lambda *a, **k: sb)
    return SandboxComparator(), sb


async def test_check_accepts_on_exit_zero(monkeypatch: pytest.MonkeyPatch) -> None:
    checker, sb = _checker(monkeypatch, comparator=_ok(_ACCEPT_OUT))
    outcome = await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    assert outcome.ok
    assert outcome.stage == "comparator"
    # .lake reset, staging reset, the three staged inputs, the unpack, then
    # the comparator invocation -- in that order.
    assert sb.events == [
        ("exec", [RESET_SCRIPT]),
        ("exec", STAGING_RESET_CMD),
        ("write", CHALLENGE_PATH),
        ("write", SUBMISSION_TAR_PATH),
        ("write", CONFIG_PATH),
        ("exec", UNPACK_CMD),
        ("exec", COMPARATOR_CMD),
    ]


async def test_check_stages_challenge_submission_config(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, sb = _checker(monkeypatch, comparator=_ok(_ACCEPT_OUT))
    tar = _tar_of({
        "./Spec.lean": "THE SOLUTION",
        "./Helpers/Aux.lean": "AUX",
        "./notes.md": "not a module",
    })
    await checker.check("THE SPEC", tar, decl="Foo.bar", claim="disproof")
    # Challenge = the spec verbatim; the submission = the sanitized archive of
    # exactly the tar's Lean modules.
    assert sb.written[CHALLENGE_PATH] == "THE SPEC"
    assert _members(cast(bytes, sb.written[SUBMISSION_TAR_PATH])) == {
        "Spec.lean": b"THE SOLUTION",
        "Helpers/Aux.lean": b"AUX",
    }
    # The config targets the .disproof theorem for a disproof claim, and the
    # solution is the agent's own entry module.
    config = json.loads(cast(str, sb.written[CONFIG_PATH]))
    assert config["theorem_names"] == ["Foo.bar.disproof"]
    assert config["challenge_module"] == "Challenge"
    assert config["solution_module"] == "Submission.Spec"
    assert config["permitted_axioms"] == ["propext", "Classical.choice", "Quot.sound"]


async def test_check_only_the_comparator_run_drops_privilege(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # The comparator image stays root for Inspect's benefit, so the privilege
    # drop lives on the exec calls: the comparator run carries
    # user=COMPARATOR_USER. The .lake reset stays root so its rm can clear
    # permission traps the untrusted build may leave in .lake; the staging
    # reset and the unpack stay root so the staged inputs are root-owned and
    # thus read-only to the build.
    checker, sb = _checker(monkeypatch, comparator=_ok(_ACCEPT_OUT))
    await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    assert sb.commands == [[RESET_SCRIPT], STAGING_RESET_CMD, UNPACK_CMD, COMPARATOR_CMD]
    assert [kw.get("user") for kw in sb.exec_kwargs] == [
        None, None, None, COMPARATOR_USER
    ]


async def test_check_proof_claim_targets_bare_decl(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker, sb = _checker(monkeypatch, comparator=_ok(_ACCEPT_OUT))
    await checker.check(SPEC, SUBMISSION_TAR, decl="Foo.bar", claim="proof")
    assert json.loads(cast(str, sb.written[CONFIG_PATH]))["theorem_names"] == ["Foo.bar"]


async def test_check_rejects_invalid_submission_before_touching_sandbox(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A submission tar with no Spec.lean is a verdict, decided host-side: the
    # sandbox is never touched (no reset, no comparator run).
    checker, sb = _checker(monkeypatch, comparator=_ok(_ACCEPT_OUT))
    outcome = await checker.check(SPEC, _tar_of({"./Other.lean": "x"}),
                                  decl="tgt", claim="proof")
    assert not outcome.ok
    assert outcome.stage == "entry_missing"
    assert "no Submission/Spec.lean" in outcome.detail
    assert sb.commands == []
    assert sb.written == {}


async def test_check_rejects_when_comparator_failed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Any nonzero comparator exit is a verdict on the submission.
    out = (
        "Building Challenge\nBuilding Submission.Spec\n"
        "uncaught exception: Illegal axiom detected: 'sorryAx'"
    )
    checker, _ = _checker(monkeypatch, comparator=_fail(1, out))
    outcome = await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    assert not outcome.ok
    assert outcome.stage == "comparator"


async def test_check_rejects_without_relying_on_phase_marker(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Output is bounded and submission-controlled, so even a failure with no
    # solution marker is classified solely by the comparator's nonzero exit.
    out = "Building Challenge\nerror: challenge spec failed to build"
    checker, _ = _checker(monkeypatch, comparator=_fail(1, out))
    outcome = await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    assert not outcome.ok
    assert outcome.stage == "comparator"


async def test_check_raises_when_reset_fails(monkeypatch: pytest.MonkeyPatch) -> None:
    # The .lake reset is a reference step; its failure is our infrastructure.
    checker, sb = _checker(monkeypatch, reset=_fail(1, stderr="reset boom"),
                           comparator=_ok(_ACCEPT_OUT))
    with pytest.raises(RuntimeError, match=r"\.lake reset failed"):
        await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    # Nothing ran past the failed reset.
    assert sb.commands == [[RESET_SCRIPT]]


async def test_check_raises_when_staging_reset_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Recreating run/ and Submission/ is likewise a reference step.
    checker, sb = _checker(monkeypatch, staging=_fail(1, stderr="mkdir boom"),
                           comparator=_ok(_ACCEPT_OUT))
    with pytest.raises(RuntimeError, match="staging reset failed"):
        await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    # Nothing ran past the failed staging reset (and nothing was staged).
    assert sb.commands == [[RESET_SCRIPT], STAGING_RESET_CMD]
    assert sb.written == {}


async def test_check_raises_when_unpack_fails(monkeypatch: pytest.MonkeyPatch) -> None:
    # Unpacking the sanitized archive is trusted too: the archive is ours, so a
    # failure there is our infrastructure, not a verdict.
    checker, sb = _checker(monkeypatch, unpack=_fail(2, stderr="tar boom"),
                           comparator=_ok(_ACCEPT_OUT))
    with pytest.raises(RuntimeError, match="submission unpack failed"):
        await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    # The comparator never ran.
    assert sb.commands == [[RESET_SCRIPT], STAGING_RESET_CMD, UNPACK_CMD]


async def test_check_maps_resource_death(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A signal-style exit is a resource-stage rejection even when the bounded
    # output provides no indication of Comparator's internal phase.
    checker, _ = _checker(monkeypatch, comparator=_fail(137))
    outcome = await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    assert not outcome.ok
    assert outcome.stage == "comparator_resource"


async def test_check_maps_timeout(monkeypatch: pytest.MonkeyPatch) -> None:
    checker, _ = _checker(monkeypatch, comparator=TimeoutError("timed out"))
    outcome = await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    assert not outcome.ok
    assert outcome.stage == "comparator_timeout"


async def test_check_maps_decode_error(monkeypatch: pytest.MonkeyPatch) -> None:
    exc = UnicodeDecodeError("utf-8", b"\xff", 0, 1, "invalid start byte")
    checker, _ = _checker(monkeypatch, comparator=exc)
    outcome = await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    assert not outcome.ok
    assert outcome.stage == "comparator"


async def test_check_maps_output_limit(monkeypatch: pytest.MonkeyPatch) -> None:
    # A stream past Inspect's exec output cap is submission-controlled (the
    # trusted phases print a handful of lines), so it scores INCORRECT rather
    # than raising -- printing 10 MiB must not error the sample.
    exc = OutputLimitExceededError(limit_str="10 MiB", truncated_output=None)
    checker, _ = _checker(monkeypatch, comparator=exc)
    outcome = await checker.check(SPEC, SUBMISSION_TAR, decl="tgt", claim="proof")
    assert not outcome.ok
    assert outcome.stage == "comparator_output_limit"


# --------------------------------------------------------------------------- #
# Scorer wiring                                                                #
# --------------------------------------------------------------------------- #
def _state(store: FakeStore) -> TaskState:
    st = TaskState(
        model=ModelName("mockllm/model"),
        sample_id="t",
        epoch=1,
        input=SPEC,
        messages=[],
        metadata={"sketch": SPEC, "decl_name": "tgt"},
    )
    return st


async def _score(
    checker: ProofChecker,
    tar: bytes,
    monkeypatch: pytest.MonkeyPatch,
    store: FakeStore | None = None,
) -> Score:
    store = store if store is not None else FakeStore()
    monkeypatch.setattr(scorer_mod, "sandbox", lambda *a, **k: FakeSandbox(tar))
    monkeypatch.setattr(scorer_mod, "store", lambda: store)
    result = await proof_scorer(checker)(_state(store), Target(""))
    assert result is not None
    return result


async def test_scorer_hands_spec_tar_decl_claim_to_checker(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    tar = _tar_of({"./Spec.lean": "sol"})
    checker = StubChecker(True)
    store = FakeStore({CLAIM_STORE_KEY: "disproof"})
    score = await _score(checker, tar, monkeypatch, store)
    assert score.value == CORRECT
    # The checker got the spec, the raw tar, the decl name, and the claim.
    (spec, got_tar, decl, claim) = checker.calls[0]
    assert spec == SPEC
    assert got_tar == tar
    assert decl == "tgt"
    assert claim == "disproof"


async def test_scorer_defaults_claim_to_proof(monkeypatch: pytest.MonkeyPatch) -> None:
    # A sample scored without ever recording a claim (e.g. it hit its limits)
    # defaults to "proof".
    checker = StubChecker(False)
    score = await _score(checker, _tar_of({"./Spec.lean": "x"}), monkeypatch)
    assert checker.calls[0][3] == "proof"
    assert score.value == INCORRECT


async def test_scorer_incorrect_when_checker_rejects(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    score = await _score(StubChecker(False), _tar_of({"./Spec.lean": "x"}), monkeypatch)
    assert score.value == INCORRECT


async def test_scorer_incorrect_when_submission_too_large(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # The agent's Submission/ is too large to read out of the sandbox
    # (read_submission_tar's read_file raises OutputLimitExceededError). That is
    # agent-caused and deterministic, so the scorer returns INCORRECT with an
    # oversize stage rather than letting it error the sample. With no tar there
    # is nothing to verify -- the checker never runs.
    class OversizeSandbox:
        async def exec(self, cmd: list[str], **kwargs: object) -> ExecResult[str]:
            return ExecResult(success=True, returncode=0, stdout="", stderr="")

        async def read_file(self, file: str, text: bool = True) -> bytes:
            raise OutputLimitExceededError(limit_str="100 MiB", truncated_output=None)

    store = FakeStore()
    monkeypatch.setattr(scorer_mod, "sandbox", lambda *a, **k: OversizeSandbox())
    monkeypatch.setattr(scorer_mod, "store", lambda: store)
    checker = StubChecker(True)
    score = await proof_scorer(checker)(_state(store), Target(""))
    assert score is not None
    assert score.value == INCORRECT
    assert score.metadata is not None
    assert score.metadata["stage"] == "submission_oversize"
    assert checker.calls == []


async def test_scorer_metadata_shape(monkeypatch: pytest.MonkeyPatch) -> None:
    # Score.metadata carries the verdict/verifier fields and the claim -- never
    # the tree (which lives on sample metadata) and no answer.
    score = await _score(StubChecker(True), _tar_of({"./Spec.lean": "x"}), monkeypatch)
    assert score.answer is None
    assert score.metadata is not None
    assert set(score.metadata) == {"stage", "claim", "verifier_output"}
    assert score.metadata["stage"] == "stub"


async def test_scorer_records_submission_tree_on_sample_metadata(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # The scorer builds the display tree from the same tar it reads and stores it
    # on *sample* metadata (so the log viewer / extract_plaintext can render it),
    # not on Score.metadata.
    tar = _tar_of(
        {"Spec.lean": "import X\ntheorem tgt := by sorry\n", "Helpers/Aux.lean": "theorem aux := trivial\n"}
    )
    store = FakeStore()
    state = _state(store)
    monkeypatch.setattr(scorer_mod, "sandbox", lambda *a, **k: FakeSandbox(tar))
    monkeypatch.setattr(scorer_mod, "store", lambda: store)
    await proof_scorer(StubChecker(True))(state, Target(""))

    assert state.metadata["submission_contents"] == {
        "Spec.lean": "import X\ntheorem tgt := by sorry\n",
        "Helpers": {"Aux.lean": "theorem aux := trivial\n"},
    }


async def test_scorer_writes_attempt_sidecar(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Per attempt, the scored Submission/ tar is written to an attempt-indexed
    # sidecar under <logdir>/artifacts/<uuid>/. Stub the private sample_active so
    # the log dir resolves to tmp_path.
    import inspect_ai.log._samples as samples_mod

    monkeypatch.setattr(
        samples_mod,
        "sample_active",
        lambda: SimpleNamespace(log_location=str(tmp_path / "run.eval")),
    )
    tar = _tar_of({"./Spec.lean": "the-submission"})
    await _score(StubChecker(True), tar, monkeypatch)
    sidecars = list((tmp_path / "artifacts").rglob("attempt-*.tar"))
    assert len(sidecars) == 1
    assert sidecars[0].read_bytes() == tar
