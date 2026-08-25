"""Integration tests for single-file submissions against the real comparator image.

These exercise the *actual* :class:`apn.checker.SandboxComparator` against the
real ``comparator`` sandbox (Lean + Mathlib + FormalConjectures + the Comparator
binary + lean4export + landrun), built from ``apn/lean/Dockerfile`` via the
production compose file. Nothing is reimplemented and no image is referenced by
a fixed tag: the compose carries ``build:`` sections, so docker (re)builds the
version-tagged image from the current Dockerfile, cache-backed -- a stale
prebuilt image can never silently satisfy the test. The sandbox is brought up
through Inspect's own lifecycle (``task_init`` /
``init_sandbox_environments_sample`` / ``cleanup``), the same path a real eval
uses, and the compose's ``read_only`` + tmpfs hardening is exercised too.

We call ``SandboxComparator().check(spec, submission, decl, claim)`` with
``apn.checker.sandbox`` pointed at the live comparator env, so the verdict here
is exactly the one the scorer would return for that submission.

What they cover (the soundness-relevant behaviour of the single-file model; the
plumbing -- tar shaping, verdict mapping -- is unit-tested in ``test_checker.py``):

* a single-file proof is accepted;
* a single-file disproof is accepted under the ``disproof`` claim;
* **a submission that ``import``s a helper module of its own is rejected** --
  the load-bearing single-file guard. Only ``Spec.lean`` becomes
  ``run/Solution.lean``; ``Submission`` is not a registered Lake library, so
  ``import Submission.…`` does not resolve and the solution build fails;
* a pattern-matching ``def`` in the entry module + a real proof is accepted --
  the module-name story (Challenge and Solution are different modules by design,
  so this confirms a faithful private/generated-name closure still matches);
* a missing/renamed entry module, and an empty submission, are rejected as a
  verdict (``entry_missing``), host-side, without touching the sandbox.

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
from apn.checker import Claim, CheckOutcome, SandboxComparator
from apn.dataset import OEIS_DIR, fc_commit
from apn.task import get_compose_file

_IMPORT = "import FormalConjectures.Util.ProblemImports\n"


def _tar_of(files: dict[str, str]) -> bytes:
    """Pack ``{relative path: contents}`` into a tar, as the checker expects
    (members relative to ``Submission/``). Stands in for what
    ``read_submission_tar`` produces from the agent's live sandbox."""
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w") as tf:
        for name, content in files.items():
            data = content.encode()
            info = tarfile.TarInfo(name)
            info.size = len(data)
            tf.addfile(info, io.BytesIO(data))
    return buf.getvalue()


def _spec(theorem_body: str, *, defs: str = "") -> str:
    """A challenge spec: the FC import, optional defs, the target theorem left
    as ``sorry``, and the appended ``.disproof`` declaration (the shape every
    committed Isolated spec has)."""
    return (
        _IMPORT
        + (defs + "\n" if defs else "")
        + f"theorem tgt : {theorem_body} := by sorry\n"
        + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"
    )


@asynccontextmanager
async def _comparator_env() -> AsyncIterator[SandboxEnvironment]:
    """Bring up the production compose and yield the live ``comparator`` env.

    Uses Inspect's sandbox lifecycle against ``apn.task.get_compose_file`` (which
    builds from ``apn/lean/Dockerfile``), so the image is current by
    construction. Per-test bring-up/tear-down isolates the read-only + tmpfs
    workspace between cases; the docker cache keeps repeat runs cheap.
    """
    # Dataset-agnostic suite: any dataset's image works, so use the oeis pin.
    compose = str(get_compose_file(fc_commit(OEIS_DIR), literature=False))
    task_name = "pytest_singlefile_comparator"
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
            yield envs["comparator"]
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
    monkeypatch: pytest.MonkeyPatch,
    spec: str,
    submission: dict[str, str],
    *,
    decl: str = "tgt",
    claim: Claim = "proof",
) -> CheckOutcome:
    """Run the real checker against a freshly built comparator sandbox."""
    async with _comparator_env() as env:
        monkeypatch.setattr(checker_mod, "sandbox", lambda *a, **k: env)
        return await SandboxComparator().check(spec, _tar_of(submission), decl=decl, claim=claim)


# --------------------------------------------------------------------------- #
# Tests.                                                                        #
# --------------------------------------------------------------------------- #
async def test_single_file_proof_is_accepted(monkeypatch: pytest.MonkeyPatch) -> None:
    spec = _spec("1 + 1 = 2")
    submission = {"Spec.lean": _spec("1 + 1 = 2").replace(
        "theorem tgt : 1 + 1 = 2 := by sorry", "theorem tgt : 1 + 1 = 2 := by norm_num"
    )}
    outcome = await _check(monkeypatch, spec, submission)
    assert outcome.ok, f"expected acceptance, got stage={outcome.stage}:\n{outcome.detail[-1500:]}"


async def test_single_file_disproof_is_accepted(monkeypatch: pytest.MonkeyPatch) -> None:
    # A false conjecture: the agent fills the .disproof sorry and declares the
    # disproof claim. The kept `tgt := sorry` is inert (not a config target and
    # not in tgt.disproof's closure).
    spec = _spec("1 + 1 = 3")
    submission = {"Spec.lean": _spec("1 + 1 = 3").replace(
        "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry",
        "theorem tgt.disproof : ¬ (type_of% @tgt) := by norm_num",
    )}
    outcome = await _check(monkeypatch, spec, submission, claim="disproof")
    assert outcome.ok, f"expected acceptance, got stage={outcome.stage}:\n{outcome.detail[-1500:]}"


async def test_helper_import_is_rejected(monkeypatch: pytest.MonkeyPatch) -> None:
    # The single-file guard. Even an *honest* helper is unusable: only Spec.lean
    # becomes run/Solution.lean, `Submission` is not a registered Lake library,
    # so `import Submission.Helpers.Aux` does not resolve and the solution build
    # fails -- a verdict in the solution phase (comparator has printed
    # "Building Solution" by then).
    spec = _spec("1 + 1 = 2")
    submission = {
        "Spec.lean": (
            _IMPORT
            + "import Submission.Helpers.Aux\n"
            + "theorem tgt : 1 + 1 = 2 := aux_eq\n"
            + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"
        ),
        "Helpers/Aux.lean": _IMPORT + "theorem aux_eq : 1 + 1 = 2 := by norm_num\n",
    }
    outcome = await _check(monkeypatch, spec, submission)
    assert not outcome.ok, f"a helper import must be rejected:\n{outcome.detail[-1500:]}"
    assert outcome.stage == "comparator"


async def test_pattern_matching_def_in_entry_is_accepted(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # The submission reproduces a pattern-matching def verbatim and proves the
    # theorem. Comparator builds Challenge and Solution as different modules by
    # design; this confirms a faithful proof whose closure includes
    # compiler-generated equational lemmas still matches.
    defs = "def parity : Nat → Bool\n  | 0 => true\n  | (n + 1) => !parity n"
    spec = _spec("parity 0 = true", defs=defs)
    submission = {"Spec.lean": _spec("parity 0 = true", defs=defs).replace(
        "theorem tgt : parity 0 = true := by sorry",
        "theorem tgt : parity 0 = true := by decide",
    )}
    outcome = await _check(monkeypatch, spec, submission)
    assert outcome.ok, (
        f"pattern-matching def proof should match, got stage={outcome.stage}:\n{outcome.detail[-1500:]}"
    )


async def test_missing_entry_module_is_rejected(monkeypatch: pytest.MonkeyPatch) -> None:
    # A submission whose tar omits Spec.lean: rejected host-side as a verdict.
    outcome = await _check(monkeypatch, _spec("1 + 1 = 2"),
                           {"Other.lean": _IMPORT + "theorem aux : True := trivial\n"})
    assert not outcome.ok
    assert outcome.stage == "entry_missing"


async def test_empty_submission_is_rejected(monkeypatch: pytest.MonkeyPatch) -> None:
    outcome = await _check(monkeypatch, _spec("1 + 1 = 2"), {})
    assert not outcome.ok
    assert outcome.stage == "entry_missing"
