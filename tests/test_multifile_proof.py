"""Integration tests for multi-module submissions against the real scorer image.

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

What they cover (the genuinely new, soundness-relevant behaviour the multi-file
change introduces; the plumbing -- tar shaping, path validation, verdict mapping
-- is unit-tested in ``test_checker.py``):

* a multi-file proof using a helper module is accepted;
* a ``sorry`` in a helper is rejected transitively (``safe_verify``);
* a custom axiom in a helper is rejected transitively;
* a pattern-matching ``def`` in the entry module + a real proof is accepted --
  the regression guard that the module-name flip preserves the mangled private
  (equational-lemma) names ``safe_verify`` matches by exact name;
* a missing/renamed entry module, and an empty submission, are rejected as a
  verdict (``compile_submission``; never raised, and without falling through to
  verifying the trusted target text).

The path-traversal / ``.lean``-only ingestion guard (Security A) is enforced by
the scorer *before* the checker runs and is covered by
``test_checker.py::test_scorer_rejects_illegal_paths_without_calling_checker``.

Docker is part of the test environment, so these always run -- they are not
gated or skipped. The first run builds the images (Lean + Mathlib) from the
Dockerfile; subsequent runs reuse the docker layer cache.
"""

from __future__ import annotations

import io
import tarfile
from contextlib import asynccontextmanager

from inspect_ai.util._sandbox.context import (
    cleanup_sandbox_environments_sample,
    init_sandbox_environments_sample,
)
from inspect_ai.util._sandbox.docker.docker import DockerSandboxEnvironment

import apn.checker as checker_mod
from apn.checker import SandboxSafeVerify
from apn.task import get_compose_file


def _tar_of(files: dict[str, str]) -> bytes:
    """Pack ``{relative path: contents}`` into a tar, as the checker expects.

    Members are relative to ``Submission/`` (``Spec.lean``, ``Helpers/Aux.lean``);
    the checker unpacks with ``tar -xf -C Submission`` and tar creates the helper
    subdirs. Stands in for what ``read_submission_tar`` produces from the agent's
    live sandbox.
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
async def _scorer_env():
    """Bring up the production compose and yield the live ``scorer`` env.

    Uses Inspect's sandbox lifecycle against ``apn.task.get_compose_file`` (which
    builds from ``apn/lean/Dockerfile``), so the image is current by construction.
    Per-test bring-up/tear-down -- simple and correct; the docker cache keeps
    repeat runs cheap (this is the same trade-off PortBench's test harness makes).
    """
    compose = str(get_compose_file(literature=False))
    task_name = "pytest_multifile_scorer"
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
            yield envs["scorer"]
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


async def _check(monkeypatch, target: str, submission: dict[str, str]):
    """Run the real checker against a freshly built scorer sandbox.

    ``submission`` is given as ``{relative path: contents}`` for readability and
    packed into the tar the checker actually consumes.
    """
    async with _scorer_env() as env:
        monkeypatch.setattr(checker_mod, "sandbox", lambda *a, **k: env)
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
# private equational-lemma names the module-name flip must preserve.
TARGET_PATTERN_MATCH = (
    _IMPORT
    + "\ndef parity : Nat → Bool\n  | 0 => true\n  | (n + 1) => !parity n\n"
    + "\ntheorem tgt : parity 0 = true := by sorry\n"
)

# Entry module that proves tgt via an imported helper lemma.
_SPEC_VIA_HELPER = (
    _IMPORT + "import Submission.Helpers.Aux\n" + "\ntheorem tgt : 1 + 1 = 2 := aux_eq\n"
)


# --------------------------------------------------------------------------- #
# Tests.                                                                        #
# --------------------------------------------------------------------------- #
async def test_multifile_proof_with_helper_is_accepted(monkeypatch) -> None:
    submission = {
        "Spec.lean": _SPEC_VIA_HELPER,
        "Helpers/Aux.lean": _IMPORT + "\ntheorem aux_eq : 1 + 1 = 2 := by norm_num\n",
    }
    outcome = await _check(monkeypatch, TARGET_SIMPLE, submission)
    assert outcome.ok, f"expected acceptance, got stage={outcome.stage}:\n{outcome.detail}"


async def test_sorry_in_helper_is_rejected(monkeypatch) -> None:
    submission = {
        "Spec.lean": _SPEC_VIA_HELPER,
        # Builds (warn.sorry=false) but the sorry poisons tgt transitively.
        "Helpers/Aux.lean": _IMPORT + "\ntheorem aux_eq : 1 + 1 = 2 := by sorry\n",
    }
    outcome = await _check(monkeypatch, TARGET_SIMPLE, submission)
    assert not outcome.ok, f"a sorry in a helper must be rejected:\n{outcome.detail}"
    assert outcome.stage == "safeverify"


async def test_custom_axiom_in_helper_is_rejected(monkeypatch) -> None:
    submission = {
        "Spec.lean": _SPEC_VIA_HELPER,
        "Helpers/Aux.lean": (
            _IMPORT
            + "\naxiom bad_ax : 1 + 1 = 2\n"
            + "\ntheorem aux_eq : 1 + 1 = 2 := bad_ax\n"
        ),
    }
    outcome = await _check(monkeypatch, TARGET_SIMPLE, submission)
    assert not outcome.ok, f"a custom axiom in a helper must be rejected:\n{outcome.detail}"
    assert outcome.stage == "safeverify"


async def test_pattern_matching_def_in_entry_is_accepted(monkeypatch) -> None:
    # Regression guard for the flip: the submission reproduces the pattern-
    # matching def verbatim and proves the theorem. Its compiler-generated
    # private equational lemmas mangle with the module name Submission.Spec --
    # the same name the target got from the flip -- so safe_verify's exact-name
    # match succeeds. A single entry module (no helper) deliberately.
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


async def test_missing_entry_module_is_rejected(monkeypatch) -> None:
    # Only a helper, no Spec.lean: rejected as a verdict, never raised, and
    # without falling through to verifying the trusted target text.
    submission = {"Helpers/Aux.lean": _IMPORT + "\ntheorem aux_eq : True := trivial\n"}
    outcome = await _check(monkeypatch, TARGET_SIMPLE, submission)
    assert not outcome.ok
    assert outcome.stage == "compile_submission"


async def test_empty_submission_is_rejected(monkeypatch) -> None:
    outcome = await _check(monkeypatch, TARGET_SIMPLE, {})
    assert not outcome.ok
    assert outcome.stage == "compile_submission"
