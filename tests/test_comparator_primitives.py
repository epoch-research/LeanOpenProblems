"""The primitive/builtin-constants invariant (comparator-migration-plan.md §2.3).

Comparator asks lean4export for a fixed set of primitive and builtin constant
names in *both* environments on every check (``primitiveTargets`` +
``builtinTargets`` in the pinned comparator's ``Main.lean``); lean4export
*panics* on a missing constant (comparator does not pass ``--ignore-missing``),
so a name absent from the dataset toolchain's environment would fail **every**
check loudly. This test asserts, directly at the toolchain level, that every one
of those names resolves in the dataset environment -- a cheap guard that a
comparator bump (which may add primitives) or a dataset FC-pin bump (a different
toolchain) has not left one dangling.

Kept in sync by hand with the pinned comparator's ``Main.lean``
(``COMPARATOR_COMMIT`` in ``apn/lean/Dockerfile``); on a comparator bump, update
``PRIMITIVE_TARGETS`` / ``BUILTIN_TARGETS`` below and re-run.

Runs the check in the ``generate`` sandbox (base Lean + Mathlib +
FormalConjectures), brought up through Inspect's lifecycle like the isolation
suites. Docker is part of the test environment, so this always runs.
"""

from __future__ import annotations

from apn.dataset import OEIS_DIR, fc_commit, fc_profile
from scripts.isolation import CONTAINER_PROJECT
from tests.lean_sandbox import generate_env

# From the pinned comparator's Comparator/Main.lean (`primitiveTargets` and
# `builtinTargets`). Nat.zero/Nat.succ are commented out upstream (the kernel
# adds them with Nat), so they are intentionally absent here.
PRIMITIVE_TARGETS = [
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
    "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft",
    "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce",
]
# builtinTargets: the base four plus the Quot family (added when Quot.sound is a
# permitted axiom, which it always is for us).
BUILTIN_TARGETS = [
    "Nat", "String", "String.mk", "Char",
    "Quot", "Quot.mk", "Quot.lift", "Quot.ind",
]


async def test_primitive_and_builtin_targets_resolve() -> None:
    """Every comparator primitive/builtin target resolves in the dataset env."""
    pin = fc_commit(OEIS_DIR)
    names = PRIMITIVE_TARGETS + BUILTIN_TARGETS
    name_list = "\n".join(f"  `{n}," for n in names)
    probe = (
        f"import {fc_profile(pin).util_module}\n"
        "open Lean\n"
        "run_cmd do\n"
        "  let env ← getEnv\n"
        f"  let names : List Name := [\n{name_list}\n  ]\n"
        "  for n in names do\n"
        "    unless env.contains n do\n"
        '      throwError "missing primitive/builtin constant: {n}"\n'
    )
    async with generate_env("pytest_comparator_primitives", pin) as env:
        await env.write_file(f"{CONTAINER_PROJECT}/_apn_primitives.lean", probe)
        # A missing constant makes the run_cmd throw -> nonzero exit + the
        # message naming it; a clean compile means every name resolved.
        res = await env.exec(
            ["lake", "env", "lean", "_apn_primitives.lean"],
            cwd=CONTAINER_PROJECT,
        )
    assert res.success, (
        "a comparator primitive/builtin target does not resolve in the dataset "
        f"environment:\n{res.stdout}\n{res.stderr}"
    )
