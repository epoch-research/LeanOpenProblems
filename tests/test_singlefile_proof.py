"""Integration tests for single-file submissions against the real scorer image.

These exercise the *actual* :class:`apn.checker.SandboxSafeVerify` against the
real ``scorer`` sandbox (Lean + Mathlib + FormalConjectures + the vendored
``safe_verify``), built from ``apn/lean/Dockerfile`` via the production compose
file. Nothing is reimplemented and no image is referenced by a fixed tag: the
compose carries ``build:`` sections, so docker (re)builds the version-tagged
image from the current Dockerfile, cache-backed -- a stale prebuilt image can
never silently satisfy the test. The sandbox is brought up through Inspect's own
lifecycle (``task_init`` / ``init_sandbox_environments_sample`` / ``cleanup``),
the same path a real eval uses, mirroring ``PortBench/test/test_sandboxes.py``.

We then call ``SandboxSafeVerify(sandbox_name="scorer").check(target, submission)``
with ``apn.checker.sandbox`` pointed at the live scorer env, so the verdict here
is exactly the one the scorer would return for that submission.

What they cover (the soundness-relevant behaviour of the single-file model; the
plumbing -- tar shaping, verdict mapping -- is unit-tested in ``test_checker.py``):

* a single-file proof is accepted;
* **a submission that ``import``s a helper module of its own is rejected at
  ``compile_submission``** -- the load-bearing single-file guard. The submission
  is compiled standalone, ``Submission`` is not a registered Lake library, and no
  helper olean is ever built, so ``import Submission.…`` does not resolve. This is
  what closes the trusted-helper hole: ``safe_verify`` kernel-replays only the
  file it is handed, trusting an *imported* module's constants rather than
  re-checking them, so there must be no way to introduce one;
* a pattern-matching ``def`` in the entry module + a real proof is accepted --
  the regression guard that compiling both sides at the same path preserves the
  mangled private (equational-lemma) names ``safe_verify`` matches by exact name;
* a missing/renamed entry module, and an empty submission, are rejected as a
  verdict (``compile_submission``; never raised, and without falling through to
  verifying the trusted target text).

Docker is part of the test environment, so these always run -- they are not
gated or skipped. The first run builds the images (Lean + Mathlib) from the
Dockerfile; subsequent runs reuse the docker layer cache.
"""

from __future__ import annotations

import io
import tarfile
from collections.abc import AsyncIterator
from contextlib import asynccontextmanager

import pytest
from inspect_ai.util import SandboxEnvironment
from inspect_ai.util._sandbox.context import (
    cleanup_sandbox_environments_sample,
    init_sandbox_environments_sample,
)
from inspect_ai.util._sandbox.docker.docker import DockerSandboxEnvironment

import apn.checker as checker_mod
from apn.checker import CheckOutcome, SandboxSafeVerify
from apn.task import get_compose_file


def _tar_of(files: dict[str, str]) -> bytes:
    """Pack ``{relative path: contents}`` into a tar, as the checker expects.

    Members are relative to ``Submission/`` (``Spec.lean``); the checker unpacks
    with ``tar -xf -C Submission``. Stands in for what ``read_submission_tar``
    produces from the agent's live sandbox.
    """
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w") as tf:
        for name, content in files.items():
            data = content.encode()
            info = tarfile.TarInfo(name)
            info.size = len(data)
            tf.addfile(info, io.BytesIO(data))
    return buf.getvalue()


@asynccontextmanager
async def _sandbox_envs() -> AsyncIterator[dict[str, SandboxEnvironment]]:
    """Bring up the production compose and yield the live sandbox-env dict.

    Uses Inspect's sandbox lifecycle against ``apn.task.get_compose_file`` (which
    builds from ``apn/lean/Dockerfile``), so the image is current by construction.
    The checker needs both the untrusted ``compile`` sandbox and the trusted
    ``scorer`` sandbox, so we expose the whole ``{name: env}`` dict. Per-test
    bring-up/tear-down -- simple and correct; the docker cache keeps repeat runs
    cheap (the same trade-off PortBench's test harness makes).
    """
    compose = str(get_compose_file(literature=False))
    task_name = "pytest_singlefile_scorer"
    await DockerSandboxEnvironment.task_init(task_name, compose)
    try:
        envs = await init_sandbox_environments_sample(
            sandboxenv_type=DockerSandboxEnvironment,
            task_name=task_name,
            config=compose,
            files={},
            setup=None,
            metadata={},
        )
        try:
            yield envs
        finally:
            await cleanup_sandbox_environments_sample(
                type="docker",
                task_name=task_name,
                config=compose,
                environments=envs,
                interrupted=False,
            )
    finally:
        await DockerSandboxEnvironment.task_cleanup(task_name, compose, cleanup=True)


async def _check(
    monkeypatch: pytest.MonkeyPatch, target: str, submission: dict[str, str]
) -> CheckOutcome:
    """Run the real checker against freshly built compile + scorer sandboxes.

    ``submission`` is given as ``{relative path: contents}`` for readability and
    packed into the tar the checker actually consumes. ``checker_mod.sandbox`` is
    pointed at the live envs by name, so ``sandbox("compile")`` /
    ``sandbox("scorer")`` resolve to the matching containers.
    """
    async with _sandbox_envs() as envs:
        monkeypatch.setattr(checker_mod, "sandbox", lambda name=None, *a, **k: envs[name])
        return await SandboxSafeVerify(sandbox_name="scorer").check(
            target, _tar_of(submission)
        )


# --------------------------------------------------------------------------- #
# Minimal Lean specs/proofs (compile against ProblemImports).                  #
# --------------------------------------------------------------------------- #
_IMPORT = "import FormalConjectures.Util.ProblemImports\n"

# A trivial trusted target with no definitions, proof left as sorry.
TARGET_SIMPLE = _IMPORT + "\ntheorem tgt : 1 + 1 = 2 := by sorry\n"

# A target whose statement is about a pattern-matching def -- isolates the
# private equational-lemma names the same-path compile must preserve.
TARGET_PATTERN_MATCH = (
    _IMPORT
    + "\ndef parity : Nat → Bool\n  | 0 => true\n  | (n + 1) => !parity n\n"
    + "\ntheorem tgt : parity 0 = true := by sorry\n"
)


# --------------------------------------------------------------------------- #
# Tests.                                                                        #
# --------------------------------------------------------------------------- #
async def test_single_file_proof_is_accepted(monkeypatch: pytest.MonkeyPatch) -> None:
    submission = {"Spec.lean": _IMPORT + "\ntheorem tgt : 1 + 1 = 2 := by norm_num\n"}
    outcome = await _check(monkeypatch, TARGET_SIMPLE, submission)
    assert outcome.ok, f"expected acceptance, got stage={outcome.stage}:\n{outcome.detail}"


async def test_helper_import_is_rejected_at_compile(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # The single-file guard. Even an *honest* helper is unusable: the submission
    # is compiled standalone and `Submission` is not a registered Lake library,
    # so `import Submission.Helpers.Aux` does not resolve and the whole
    # submission fails to compile -- never reaching safe_verify. This is what
    # prevents an agent from smuggling a kernel-invalid constant into an
    # imported (and therefore *trusted*, not replayed) helper module.
    submission = {
        "Spec.lean": (
            _IMPORT + "import Submission.Helpers.Aux\n\ntheorem tgt : 1 + 1 = 2 := aux_eq\n"
        ),
        "Helpers/Aux.lean": _IMPORT + "\ntheorem aux_eq : 1 + 1 = 2 := by norm_num\n",
    }
    outcome = await _check(monkeypatch, TARGET_SIMPLE, submission)
    assert not outcome.ok, f"a helper import must be rejected:\n{outcome.detail}"
    assert outcome.stage == "compile_submission"


async def test_pattern_matching_def_in_entry_is_accepted(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Regression guard: the submission reproduces the pattern-matching def
    # verbatim and proves the theorem. Its compiler-generated private equational
    # lemmas mangle with the module name Submission.Spec -- the same name the
    # target got by compiling at the same path -- so safe_verify's exact-name
    # match succeeds.
    submission = {
        "Spec.lean": (
            _IMPORT
            + "\ndef parity : Nat → Bool\n  | 0 => true\n  | (n + 1) => !parity n\n"
            + "\ntheorem tgt : parity 0 = true := by decide\n"
        ),
    }
    outcome = await _check(monkeypatch, TARGET_PATTERN_MATCH, submission)
    assert outcome.ok, (
        f"pattern-matching def proof should match private names, got "
        f"stage={outcome.stage}:\n{outcome.detail}"
    )


async def test_missing_entry_module_is_rejected(monkeypatch: pytest.MonkeyPatch) -> None:
    # A submission whose tar omits Spec.lean: rejected as a verdict, never
    # raised, and without falling through to verifying the trusted target text.
    submission = {"Other.lean": _IMPORT + "\ntheorem aux_eq : True := trivial\n"}
    outcome = await _check(monkeypatch, TARGET_SIMPLE, submission)
    assert not outcome.ok
    assert outcome.stage == "compile_submission"


async def test_empty_submission_is_rejected(monkeypatch: pytest.MonkeyPatch) -> None:
    outcome = await _check(monkeypatch, TARGET_SIMPLE, {})
    assert not outcome.ok
    assert outcome.stage == "compile_submission"
