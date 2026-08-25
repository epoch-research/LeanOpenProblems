"""Comparator soundness properties that span more than one check, plus the
disproof-match semantic delta (comparator-migration-plan.md §3.1, §4, §6).

Unlike ``test_lean_vuln_e2e.py`` (one fresh sandbox per case), these drive
*several* ``SandboxComparator.check`` calls against **one** live comparator
sandbox, because the property under test is cross-check: does the per-check
workspace reset scrub a prior submission's filesystem poisoning? They also pin
the disproof-shape verdicts that changed when the match became syntactic BEq
over export-parsed terms instead of SafeVerify's kernel defeq.

The submissions here run real compile-time ``#eval`` inside the comparator
container's landrun sandbox, against the read-only rootfs -- so this is also the
end-to-end exercise of the §3.1 hardening.

Docker is part of the test environment, so these always run; the first run
builds the image, later runs hit the layer cache.
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


def _tar_of(spec_text: str) -> bytes:
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w") as tf:
        data = spec_text.encode()
        info = tarfile.TarInfo("./Spec.lean")
        info.size = len(data)
        tf.addfile(info, io.BytesIO(data))
    return buf.getvalue()


def _spec(body: str) -> str:
    return (
        _IMPORT
        + f"theorem tgt : {body} := by sorry\n"
        + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"
    )


@asynccontextmanager
async def _comparator_env() -> AsyncIterator[SandboxEnvironment]:
    compose = str(get_compose_file(fc_commit(OEIS_DIR), literature=False))
    task_name = "pytest_comparator_security"
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
    env: SandboxEnvironment,
    monkeypatch: pytest.MonkeyPatch,
    spec: str,
    submission: str,
    *,
    claim: Claim = "proof",
) -> CheckOutcome:
    monkeypatch.setattr(checker_mod, "sandbox", lambda *a, **k: env)
    return await SandboxComparator().check(spec, _tar_of(submission), decl="tgt", claim=claim)


# --------------------------------------------------------------------------- #
# Cross-attempt filesystem poisoning (§3.1 item 1; §6).                        #
# --------------------------------------------------------------------------- #
# A compile-time #eval that, during `lake build Solution`, replaces the
# writable `.lake/packages` symlink (into the read-only pristine tree) with a
# poisoned real directory. landrun grants writes to `.lake`, so the swap
# succeeds *within* the check; the next check's reset-workspace.sh must undo it
# before that check's trusted Challenge builds against Mathlib. Needs no import:
# IO.FS is in core (Init).
_POISON_PACKAGES = (
    '#eval (do\n'
    '  let pkgs := "/workspace/leanproject/.lake/packages"\n'
    '  try IO.FS.removeFile pkgs catch _ => pure ()\n'
    '  try (IO.Process.output { cmd := "rm", args := #["-rf", pkgs] } *> pure ()) catch _ => pure ()\n'
    '  try IO.FS.createDirAll (pkgs ++ "/mathlib") catch _ => pure ()\n'
    '  : IO Unit)\n'
)


async def test_cross_attempt_filesystem_poisoning_is_scrubbed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Check #1's submission swaps the Mathlib packages symlink for a poisoned
    directory during its build; check #2's honest proof must still be ACCEPTED,
    proving the per-check reset restored the pristine Mathlib before check #2's
    Challenge built. (This asserts the quiescent filesystem-reset + RO-rootfs
    story only; it is deliberately not evidence that a hostile *process* was
    removed -- see the process-survival test below.)"""
    async with _comparator_env() as env:
        # Check #1: a wrong proof (sorry) that also tries to poison packages.
        # It is rejected either way; what matters is the side effect.
        poison_submission = _IMPORT + _POISON_PACKAGES + (
            "theorem tgt : 1 + 1 = 2 := by sorry\n"
            "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"
        )
        first = await _check(env, monkeypatch, _spec("1 + 1 = 2"), poison_submission)
        assert not first.ok, "the poisoning submission is a wrong proof; it must reject"

        # Check #2: an honest proof. If the poison survived, this check's
        # Challenge build would not find Mathlib and the challenge phase would
        # raise; acceptance proves the reset restored the pristine packages.
        honest = _IMPORT + (
            "theorem tgt : 1 + 1 = 2 := by norm_num\n"
            "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"
        )
        second = await _check(env, monkeypatch, _spec("1 + 1 = 2"), honest)
        assert second.ok, (
            f"honest proof after a poisoning attempt was not accepted "
            f"(reset failed to restore Mathlib?): stage={second.stage}\n{second.detail[-1500:]}"
        )


# Note on cross-attempt *process* isolation (plan §3.1 item 2): Inspect exposes
# no per-service restart (issue #5034), so reset-workspace.sh -- a filesystem
# reset -- cannot by itself terminate a process a prior check left running. That
# remains the documented known limitation. We deliberately ship no test
# asserting a specific process-survival outcome: empirically, in the Docker
# backend a solution-build child detached via setsid does not outlive the check
# (tini `init: true` + landrun tear it down, and landrun's inherited Landlock
# domain confines any survivor to `.lake`), but that is incidental
# defense-in-depth, not a guarantee, and may differ on k8s -- so it is not
# something to pin as a passing test.


# --------------------------------------------------------------------------- #
# Disproof-match semantic delta (§4, §6): the match is now syntactic BEq over  #
# export-parsed (mdata-stripped) terms, not SafeVerify's kernel defeq.         #
# --------------------------------------------------------------------------- #
async def test_disproof_exact_not_forall_accepts(monkeypatch: pytest.MonkeyPatch) -> None:
    """The by-construction happy path: the agent keeps the file's own
    ``type_of%`` disproof line and fills its sorry. Its type is exactly the
    challenge's, so BEq matches."""
    spec = _spec("∀ n : Nat, n + 2 = n")
    submission = _IMPORT + (
        "theorem tgt : ∀ n : Nat, n + 2 = n := by sorry\n"
        "theorem tgt.disproof : ¬ (type_of% @tgt) := by intro h; have := h 0; omega\n"
    )
    async with _comparator_env() as env:
        outcome = await _check(env, monkeypatch, spec, submission, claim="disproof")
    assert outcome.ok, f"exact type_of% disproof should accept: {outcome.stage}\n{outcome.detail[-1200:]}"


async def test_disproof_restated_negation_accepts(monkeypatch: pytest.MonkeyPatch) -> None:
    """Restating the negation as an explicit ``¬ (∀ …)`` -- syntactically the
    same ``Not (∀ …)`` the challenge elaborates to -- also accepts. (Binder
    *names* live under Not's lambda and Expr BEq is not alpha-sensitive there,
    so a renamed bound variable is fine; pinned by the next test.)"""
    spec = _spec("∀ n : Nat, n + 2 = n")
    submission = _IMPORT + (
        "theorem tgt : ∀ n : Nat, n + 2 = n := by sorry\n"
        "theorem tgt.disproof : ¬ (∀ n : Nat, n + 2 = n) := by intro h; have := h 0; omega\n"
    )
    async with _comparator_env() as env:
        outcome = await _check(env, monkeypatch, spec, submission, claim="disproof")
    assert outcome.ok, f"explicit ¬(∀ …) disproof should accept: {outcome.stage}\n{outcome.detail[-1200:]}"


async def test_disproof_false_conclusion_form_rejects(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A rewritten disproof of the shape ``(h : ∀ …) : False`` is defeq to
    ``Not (∀ …)`` but not *syntactically* it (``Not P`` unfolds to ``P → False``
    definitionally, and here the statement's own binders sit inside). SafeVerify
    accepted this via kernel defeq; Comparator's syntactic BEq rejects it. This
    pins the delta so the prompt's "fill the sorry, don't restate" guidance is
    load-bearing, not cosmetic."""
    spec = _spec("∀ n : Nat, n + 2 = n")
    submission = _IMPORT + (
        "theorem tgt : ∀ n : Nat, n + 2 = n := by sorry\n"
        "theorem tgt.disproof (h : ∀ n : Nat, n + 2 = n) : False := by have := h 0; omega\n"
    )
    async with _comparator_env() as env:
        outcome = await _check(env, monkeypatch, spec, submission, claim="disproof")
    assert not outcome.ok, (
        "a (h : ∀ …) : False disproof is not syntactically Not (∀ …); Comparator's "
        f"BEq match must reject it. stage={outcome.stage}\n{outcome.detail[-1200:]}"
    )
    assert outcome.stage == "comparator"
