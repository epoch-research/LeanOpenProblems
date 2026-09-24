"""Integration tests for submission acceptance against the real comparator image.

These exercise the *actual* :class:`apn.checker.SandboxComparator` against the
real ``comparator`` sandbox (Lean + Mathlib + FormalConjectures + the Comparator
binary + lean4export + landrun), built from ``apn/lean/Dockerfile`` via the
production compose file. Nothing is reimplemented and no image is referenced by
a fixed tag: the compose carries ``build:`` sections, so docker (re)builds the
version-tagged image from the current Dockerfile, cache-backed -- a stale
prebuilt image can never silently satisfy the test. The sandbox is brought up
through Inspect's own lifecycle (``task_init`` /
``init_sandbox_environments_sample`` / ``cleanup``), the same path a real eval
uses, so the checker's non-privileged-user execs and landrun sandboxing are
exercised too.

We call ``SandboxComparator().check(spec, submission, decl, claim)`` with
``apn.checker.sandbox`` pointed at the live comparator env, so the verdict here
is exactly the one the scorer would return for that submission.

What they cover (the acceptance side of the submission model -- a submission is
the Lean module tree under ``Submission/``, entry module ``Spec.lean``; the
plumbing -- tar sanitizing, verdict mapping -- is unit-tested in
``test_checker.py`` and the cheating attempts in ``test_lean_vuln_e2e.py``):

* a single-file proof is accepted;
* a theorem whose fully qualified name contains a dotted guillemet-quoted
  component is accepted (the shape of three live FC100 targets);
* **a proof split across helper modules is accepted** -- ``Spec.lean`` imports
  ``Submission.Helpers.Lemmas``, which imports a helper of its own; the checker
  stages the whole tree at ``Submission/`` in the comparator sandbox, where the
  image's lakefile registers the ``Submission`` library, so Lake builds the
  helpers as part of building the entry module;
* every case runs at the one battery pin (``PIN``, the OEIS pin);
  Comparator's verdict logic does not vary with the pin, and that each
  registered pin's images build and accept an honest proof and disproof is
  ``tests/test_pin_smoke.py``'s job;
* a single-file disproof is accepted under the ``disproof`` claim;
* a pattern-matching ``def`` in the entry module + a real proof is accepted --
  the module-name story (Challenge and the entry module are different modules
  by design, so this confirms a faithful private/generated-name closure still
  matches);
* a helper at a name Lake can only import with ``«»`` quoting
  (``my-helpers/Lemmas.lean``, imported as ``Submission.«my-helpers».Lemmas``) is
  staged and resolves like any other -- the checker stages every ``.lean``
  file inside the tree and leaves importability to Lake, which decides it
  identically in both sandboxes;
* a missing/renamed entry module, and an empty submission, are rejected as a
  verdict (``entry_missing``), host-side, without touching the sandbox.

Docker is part of the test environment, so these always run -- they are not
gated or skipped. The first run builds the images (Lean + Mathlib) from the
Dockerfile; subsequent runs reuse the docker layer cache.
"""

from __future__ import annotations

from collections.abc import AsyncIterator

import pytest
import pytest_asyncio
from inspect_ai.util import SandboxEnvironment

import apn.checker as checker_mod
from apn.checker import Claim, CheckOutcome, SandboxComparator
from apn.dataset import OEIS_DIR, fc_commit, fc_profile
from apn.filetree import read_submission_tar
from tests.lean_sandbox import production_envs, write_submission

PIN = fc_commit(OEIS_DIR)
IMP = f"import {fc_profile(PIN).util_module}\n"


def _spec(theorem_body: str, *, defs: str = "") -> str:
    """A challenge spec: the pin's FC import ``IMP``, optional defs, the target
    theorem left as ``sorry``, and the appended ``.disproof`` declaration (the
    shape every committed Isolated spec has)."""
    return (
        IMP
        + (defs + "\n" if defs else "")
        + f"theorem tgt : {theorem_body} := by sorry\n"
        + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"
    )


def _multi_module_submission() -> dict[str, str]:
    """An honest proof of ``1 + 1 = 2`` split across three modules: the entry
    imports ``Submission.Helpers.Lemmas``, which imports
    ``Submission.Helpers.Deep.Base``, where the actual proof lives."""
    return {
        "Spec.lean": (
            IMP
            + "import Submission.Helpers.Lemmas\n"
            + "theorem tgt : 1 + 1 = 2 := aux_eq\n"
            + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"
        ),
        "Helpers/Lemmas.lean": (
            IMP
            + "import Submission.Helpers.Deep.Base\n"
            + "theorem aux_eq : 1 + 1 = 2 := base_eq\n"
        ),
        "Helpers/Deep/Base.lean": IMP + "theorem base_eq : 1 + 1 = 2 := by norm_num\n",
    }


@pytest_asyncio.fixture(loop_scope="module", scope="module")
async def envs() -> AsyncIterator[dict[str, SandboxEnvironment]]:
    """The live sandbox envs at ``PIN`` -- the agent's ``default`` and the
    trusted ``comparator`` -- brought up **once** for the whole module.

    Every case here is honest, and ``SandboxComparator.check`` resets the
    workspace before each check, so a shared sandbox is safe -- and it builds
    the image once instead of per test, shrinking the buildkit flake surface
    (mirrors ``tests/test_gold_proofs.py``). The fixture and the cases share one
    module-scoped event loop (pytest-asyncio ``loop_scope="module"``); driving
    Inspect's sandbox lifecycle on pytest-asyncio's own loop is the only safe
    way (an ``asyncio.run`` in a plain fixture spins up a second loop its
    loop-bound globals deadlock against)."""
    async with production_envs("pytest_acceptance", PIN) as envs:
        yield envs


async def _check(
    envs: dict[str, SandboxEnvironment],
    monkeypatch: pytest.MonkeyPatch,
    spec: str,
    submission: dict[str, str],
    *,
    decl: str = "tgt",
    claim: Claim = "proof",
) -> CheckOutcome:
    """Stage ``submission`` in the agent sandbox, tar it exactly as the scorer
    does, and run the real checker against the comparator sandbox."""
    await write_submission(envs["default"], submission)
    tar = await read_submission_tar(envs["default"])
    monkeypatch.setattr(checker_mod, "sandbox", lambda *a, **k: envs["comparator"])
    return await SandboxComparator().check(spec, tar, decl=decl, claim=claim)


# --------------------------------------------------------------------------- #
# Tests.                                                                        #
# --------------------------------------------------------------------------- #
@pytest.mark.asyncio(loop_scope="module")
async def test_single_file_proof_is_accepted(
    envs: dict[str, SandboxEnvironment], monkeypatch: pytest.MonkeyPatch
) -> None:
    spec = _spec("1 + 1 = 2")
    submission = {"Spec.lean": _spec("1 + 1 = 2").replace(
        "theorem tgt : 1 + 1 = 2 := by sorry", "theorem tgt : 1 + 1 = 2 := by norm_num"
    )}
    outcome = await _check(envs, monkeypatch, spec, submission)
    assert outcome.ok, f"expected acceptance, got stage={outcome.stage}:\n{outcome.detail[-1500:]}"


@pytest.mark.asyncio(loop_scope="module")
async def test_quoted_decl_name_component_containing_dot_is_accepted(
    envs: dict[str, SandboxEnvironment], monkeypatch: pytest.MonkeyPatch
) -> None:
    """A source-spelled declaration name must round-trip through Comparator's config.

    FC100 contains three live targets under Arxiv namespaces whose quoted
    component is an arXiv identifier such as ``«0912.2382»``. This pins the
    end-to-end contract that Comparator's config decoding preserves that single
    name component.
    """
    decl = "Arxiv.«0912.2382».curling_number_conjecture"
    spec = (
        IMP
        + "namespace Arxiv.«0912.2382»\n"
        + "theorem curling_number_conjecture : 1 + 1 = 2 := by sorry\n"
        + "end Arxiv.«0912.2382»\n"
        + f"theorem {decl}.disproof : ¬ (type_of% @{decl}) := sorry\n"
    )
    submission = {
        "Spec.lean": spec.replace(
            "theorem curling_number_conjecture : 1 + 1 = 2 := by sorry",
            "theorem curling_number_conjecture : 1 + 1 = 2 := by norm_num",
        )
    }
    outcome = await _check(envs, monkeypatch, spec, submission, decl=decl)
    assert outcome.ok, (
        "a valid proof under a quoted dotted name should be accepted, got "
        f"stage={outcome.stage}:\n{outcome.detail[-1500:]}"
    )


@pytest.mark.asyncio(loop_scope="module")
async def test_multi_module_proof_is_accepted(
    envs: dict[str, SandboxEnvironment], monkeypatch: pytest.MonkeyPatch
) -> None:
    # The submission is the whole Submission/ module tree: the entry imports a
    # helper that imports another (in a nested directory). The checker stages
    # the tree at Submission/ in the comparator sandbox, where the image's
    # lakefile registers the `Submission` library, so `lake build
    # Submission.Spec` compiles both helpers first, and the full closure is
    # exported, compared and kernel-replayed.
    spec = _spec("1 + 1 = 2")
    outcome = await _check(envs, monkeypatch, spec, _multi_module_submission())
    assert outcome.ok, (
        f"a proof split across helper modules should be accepted, got "
        f"stage={outcome.stage}:\n{outcome.detail[-1500:]}"
    )


@pytest.mark.asyncio(loop_scope="module")
async def test_single_file_disproof_is_accepted(
    envs: dict[str, SandboxEnvironment], monkeypatch: pytest.MonkeyPatch
) -> None:
    # A false conjecture: the agent fills the .disproof sorry and declares the
    # disproof claim. The kept `tgt := sorry` is inert (not a config target and
    # not in tgt.disproof's closure).
    spec = _spec("1 + 1 = 3")
    submission = {"Spec.lean": _spec("1 + 1 = 3").replace(
        "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry",
        "theorem tgt.disproof : ¬ (type_of% @tgt) := by norm_num",
    )}
    outcome = await _check(envs, monkeypatch, spec, submission, claim="disproof")
    assert outcome.ok, f"expected acceptance, got stage={outcome.stage}:\n{outcome.detail[-1500:]}"


@pytest.mark.asyncio(loop_scope="module")
async def test_pattern_matching_def_in_entry_is_accepted(
    envs: dict[str, SandboxEnvironment], monkeypatch: pytest.MonkeyPatch
) -> None:
    # The submission reproduces a pattern-matching def verbatim and proves the
    # theorem. Comparator builds Challenge and the entry module
    # (Submission.Spec) as different modules by design; this confirms a
    # faithful proof whose closure includes compiler-generated equational
    # lemmas still matches.
    defs = "def parity : Nat → Bool\n  | 0 => true\n  | (n + 1) => !parity n"
    spec = _spec("parity 0 = true", defs=defs)
    submission = {"Spec.lean": _spec("parity 0 = true", defs=defs).replace(
        "theorem tgt : parity 0 = true := by sorry",
        "theorem tgt : parity 0 = true := by decide",
    )}
    outcome = await _check(envs, monkeypatch, spec, submission)
    assert outcome.ok, (
        f"pattern-matching def proof should match, got stage={outcome.stage}:\n{outcome.detail[-1500:]}"
    )


@pytest.mark.asyncio(loop_scope="module")
async def test_helper_at_quoted_module_name_is_accepted(
    envs: dict[str, SandboxEnvironment], monkeypatch: pytest.MonkeyPatch
) -> None:
    # The checker stages every `.lean` file inside the tree
    # (apn.checker.module_path) and leaves importability to Lake: a helper at
    # `my-helpers/Lemmas.lean` is the module `Submission.«my-helpers».Lemmas`, in the
    # agent's sandbox and in the comparator's alike, so what builds for the
    # agent builds for the verifier.
    spec = _spec("1 + 1 = 2")
    submission = {
        "Spec.lean": (
            IMP
            + "import Submission.«my-helpers».Lemmas\n"
            + "theorem tgt : 1 + 1 = 2 := aux_eq\n"
            + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"
        ),
        "my-helpers/Lemmas.lean": IMP + "theorem aux_eq : 1 + 1 = 2 := by norm_num\n",
    }
    outcome = await _check(envs, monkeypatch, spec, submission)
    assert outcome.ok, (
        f"a helper at a quoted module name should be accepted, got "
        f"stage={outcome.stage}:\n{outcome.detail[-1500:]}"
    )


@pytest.mark.asyncio(loop_scope="module")
async def test_missing_entry_module_is_rejected(
    envs: dict[str, SandboxEnvironment], monkeypatch: pytest.MonkeyPatch
) -> None:
    # A submission whose tar omits Spec.lean: rejected host-side as a verdict.
    outcome = await _check(envs, monkeypatch, _spec("1 + 1 = 2"),
                           {"Other.lean": IMP + "theorem aux : True := trivial\n"})
    assert not outcome.ok
    assert outcome.stage == "entry_missing"


@pytest.mark.asyncio(loop_scope="module")
async def test_empty_submission_is_rejected(
    envs: dict[str, SandboxEnvironment], monkeypatch: pytest.MonkeyPatch
) -> None:
    outcome = await _check(envs, monkeypatch, _spec("1 + 1 = 2"), {})
    assert not outcome.ok
    assert outcome.stage == "entry_missing"
