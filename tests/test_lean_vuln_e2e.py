"""End-to-end Lean *soundness* tests, written from the agent's point of view.

Every case supplies **only the agent's ``Submission/`` file tree** (a ``{relative
path: contents}`` dict) plus the challenge spec and the declared claim. The tree
is written into the live **agent** sandbox and scored by the **real**
:func:`apn.scorer.proof_scorer`, which tars it from that sandbox
(``read_submission_tar``) and verifies it in the **comparator** sandbox via
:class:`~apn.checker.SandboxComparator`. So each test exercises the exact
production path an agent submission travels -- nothing is reimplemented, and the
verdict is the one a real eval would record.

This is the security counterpart to ``test_singlefile_proof.py`` (which checks
plumbing/acceptance). Here we assert the *secure* verdict for a battery of
cheating attempts and honest baselines, re-derived from Comparator's model
rather than blind-ported from SafeVerify:

* **must REJECT** -- sorry / native_decide / custom axiom (forbidden axioms), a
  weakened or missing target statement, and a kernel-bypassing constant injected
  into the entry module (caught by comparator's full-closure kernel replay);
* **must REJECT -- any helper import.** Only Spec.lean becomes
  ``run/Solution.lean``, so an ``import Submission.…`` of a helper module does
  not resolve and the solution build fails. This keeps the trusted-helper hole
  shut: a kernel-invalid constant hidden in a helper can never be imported;
* **must ACCEPT** -- honest single-file proof, definition reproduction, a
  genuine disproof, and -- new under Comparator's model, where extra imports and
  inert unsafe decls are sound because the reachable closure is what gets
  replayed -- an entry module carrying an extra import or an unused ``unsafe``
  constant;
* **must REJECT -- root code execution.** A compile-time ``#eval`` tries to
  overwrite the lean4export binary / a Mathlib olean / the challenge source. The
  read-only rootfs + landrun sandbox make the writes fail; even if an attacker
  swallows the IO exception and lets the build succeed, the verdict must stay
  reject (the ``sorry`` is still caught). This doubles as the landrun canary.

Memory: the honest/attacker cases import ProblemImports (Mathlib) like a real
sample. Docker is part of the test environment, so -- like the sibling suite --
these always run; the first run builds the image, later runs hit the layer cache.
"""

from __future__ import annotations

from collections.abc import AsyncIterator
from contextlib import asynccontextmanager
from dataclasses import dataclass

import pytest

from inspect_ai.model import ModelName
from inspect_ai.scorer import CORRECT, Target
from inspect_ai.solver import TaskState
from inspect_ai.util import SandboxEnvironment
from inspect_ai.util._sandbox.context import (
    cleanup_sandbox_environments_sample,
    init_sandbox_environments_sample,
)
from inspect_ai.util._sandbox.docker.docker import DockerSandboxEnvironment

import apn.checker as checker_mod
import apn.scorer as scorer_mod
from apn.checker import Claim, SandboxComparator
from apn.dataset import OEIS_DIR, fc_commit
from apn.layout import SUBMISSION_DIR
from apn.scorer import CLAIM_STORE_KEY, proof_scorer
from apn.task import get_compose_file

_IMPORT = "import FormalConjectures.Util.ProblemImports\n"

# --------------------------------------------------------------------------- #
# Building blocks for the submission trees.                                    #
# --------------------------------------------------------------------------- #
# Add `fakeFalse : False := True.intro` to the environment WITHOUT a kernel
# check (`debug.skipKernelTC` routes addDecl through addDeclWithoutChecking).
# The Declaration is built by hand so the *elaborator* never sees the type/value
# mismatch either. The result carries no axioms, so an axiom-only guard would
# not catch it; only a kernel *replay* would -- which comparator does for the
# entire reachable closure. From any `False` you derive anything via `.elim`.
INJECT = (
    "import Lean\n"
    "open Lean Elab Command\n"
    "set_option debug.skipKernelTC true in\n"
    "run_cmd do\n"
    "  let decl : Declaration := .thmDecl {\n"
    "    name := `fakeFalse, levelParams := [],\n"
    "    type := .const ``False [], value := .const ``True.intro [], all := [`fakeFalse] }\n"
    "  liftCoreM (addDecl decl)\n"
)
IMPORT_AUX = "import Submission.Helpers.Aux\n"

# Code-execution attack on the verifier's TCB. The submission is *built*
# (`lake build Solution`) inside the comparator container -- but under landrun
# (writes confined to .lake) and as the non-privileged user (the binary is
# root-owned). A `#eval` of an IO action runs at elaboration time and tries to
# overwrite the lean4export binary with a script that exits 0, after which an
# export could be spoofed. The write must fail; and even if the attacker
# catches the IO exception, the kept `sorry` is still caught -> reject.
LEAN4EXPORT_BIN = "/usr/local/bin/lean4export"  # baked location (on PATH)
TAMPER_EXPORTER = (
    f'#eval (IO.FS.writeFile "{LEAN4EXPORT_BIN}" "#!/bin/sh\\nexit 0\\n" : IO Unit)\n'
    f'#eval (do let _ <- IO.Process.output '
    f'{{ cmd := "chmod", args := #["755", "{LEAN4EXPORT_BIN}"] }}; pure () : IO Unit)\n'
)


def _spec(body: str, *, defs: str = "") -> str:
    """A challenge spec in the committed shape: import, optional defs, the target
    left as ``sorry``, and the appended ``.disproof`` declaration."""
    return (
        _IMPORT
        + (defs + "\n" if defs else "")
        + f"theorem tgt : {body} := by sorry\n"
        + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"
    )


@dataclass(frozen=True)
class Case:
    label: str
    spec: str
    files: dict[str, str]
    secure_accept: bool
    claim: Claim = "proof"


CASES: list[Case] = [
    # ----------------------------- must REJECT ----------------------------- #
    Case(
        "entry_injection_caught_by_replay",
        _spec("False"),
        {"Spec.lean": _IMPORT + INJECT + "\ntheorem tgt : False := fakeFalse\n"
         + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"},
        secure_accept=False,
    ),
    Case(
        "sorry_in_entry",
        _spec("2 + 2 = 4"),
        {"Spec.lean": _spec("2 + 2 = 4")},
        secure_accept=False,
    ),
    Case(
        # The disproof-claim counterpart of sorry_in_entry, and the basic
        # soundness floor of the disproof path: submit under claim="disproof"
        # with the .disproof theorem left as sorry. Comparator targets
        # tgt.disproof, whose sorry pulls sorryAx into its axiom closure ->
        # reject. (The kept `tgt := sorry` is inert -- not the config target.)
        "sorry_in_disproof",
        _spec("2 + 2 = 5"),
        {"Spec.lean": _spec("2 + 2 = 5")},
        secure_accept=False,
        claim="disproof",
    ),
    Case(
        "native_decide_forbidden_axiom",
        _spec("2 + 2 = 4"),
        {"Spec.lean": _IMPORT + "theorem tgt : 2 + 2 = 4 := by native_decide\n"
         + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"},
        secure_accept=False,
    ),
    Case(
        "custom_axiom",
        _spec("2 + 2 = 4"),
        {"Spec.lean": _IMPORT + "axiom bad : 2 + 2 = 4\ntheorem tgt : 2 + 2 = 4 := bad\n"
         + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"},
        secure_accept=False,
    ),
    Case(
        "weakened_statement",
        _spec("∀ n : Nat, n + 0 = n"),
        {"Spec.lean": _IMPORT + "theorem tgt : True := trivial\n"
         + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"},
        secure_accept=False,
    ),
    Case(
        "missing_target_theorem",
        _spec("2 + 2 = 4"),
        {"Spec.lean": _IMPORT + "theorem other : True := trivial\n"},
        secure_accept=False,
    ),
    Case(
        "helper_import_rejected",
        _spec("2 + 2 = 4"),
        {
            "Helpers/Aux.lean": _IMPORT + "theorem aux : 2 + 2 = 4 := by norm_num\n",
            "Spec.lean": _IMPORT + IMPORT_AUX + "theorem tgt : 2 + 2 = 4 := aux\n"
            + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n",
        },
        secure_accept=False,
    ),
    Case(
        # A kernel-invalid `fakeFalse : False` hidden in a helper, used from the
        # entry. The helper import cannot resolve, so it never gets built --
        # rejected at the solution build. (Under SafeVerify this was the closed
        # trusted-helper hole; here it is an ordinary regression guard.)
        "helper_inject_false_rejected",
        _spec("False"),
        {
            "Helpers/Aux.lean": INJECT,
            "Spec.lean": _IMPORT + IMPORT_AUX + "theorem tgt : False := fakeFalse\n"
            + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n",
        },
        secure_accept=False,
    ),
    # ----------------------------- must ACCEPT ----------------------------- #
    Case(
        "honest_single_file",
        _spec("2 + 2 = 4"),
        {"Spec.lean": _IMPORT + "theorem tgt : 2 + 2 = 4 := by decide\n"
         + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"},
        secure_accept=True,
    ),
    Case(
        "honest_def_reproduction",
        _spec("foo = 7", defs="def foo : Nat := 7"),
        {"Spec.lean": _IMPORT + "def foo : Nat := 7\ntheorem tgt : foo = 7 := by decide\n"
         + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"},
        secure_accept=True,
    ),
    Case(
        "honest_disproof",
        _spec("2 + 2 = 5"),
        {"Spec.lean": _IMPORT + "theorem tgt : 2 + 2 = 5 := by sorry\n"
         + "theorem tgt.disproof : ¬ (type_of% @tgt) := by decide\n"},
        secure_accept=True,
        claim="disproof",
    ),
    # --- extra import / inert unsafe: now SOUND under Comparator's model --- #
    # Comparator replays the reachable closure and compares the configured
    # target's closure, so an extra import cannot taint the target and an
    # unused unsafe decl (unsafe decls aren't even exported) is inert. Both
    # were rejected by SafeVerify's import-superset / unsafe guards; encoded
    # here as ACCEPT cases so the suite documents the new model.
    Case(
        "extra_import_is_sound",
        _spec("True"),
        {"Spec.lean": "import Lean\n" + _IMPORT + "theorem tgt : True := trivial\n"
         + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"},
        secure_accept=True,
    ),
    Case(
        "inert_unsafe_constant_is_sound",
        _spec("2 + 2 = 4"),
        {"Spec.lean": _IMPORT + "unsafe def loop : Nat := loop\n"
         + "theorem tgt : 2 + 2 = 4 := by decide\n"
         + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"},
        secure_accept=True,
    ),
    # ---- root code execution: TCB tamper during build (must REJECT) ---- #
    Case(
        "root_exec_overwrites_exporter",
        _spec("2 + 2 = 5"),
        {"Spec.lean": _IMPORT + TAMPER_EXPORTER + "theorem tgt : 2 + 2 = 5 := by sorry\n"
         + "theorem tgt.disproof : ¬ (type_of% @tgt) := sorry\n"},
        secure_accept=False,
    ),
]


def _params() -> list[object]:
    return [pytest.param(c, id=c.label) for c in CASES]


# --------------------------------------------------------------------------- #
# Harness: write the agent's tree into the live agent sandbox, run the real    #
# scorer (which verifies in the comparator sandbox).                           #
# --------------------------------------------------------------------------- #
class _FakeStore:
    def __init__(self, claim: Claim) -> None:
        self._data: dict[str, object] = {CLAIM_STORE_KEY: claim}

    def get(self, key: str, default: object = None) -> object:
        return self._data.get(key, default)

    def set(self, key: str, value: object) -> None:
        self._data[key] = value


@asynccontextmanager
async def _sandboxes() -> AsyncIterator[dict[str, SandboxEnvironment]]:
    """Bring up the production compose; yield the live ``{name: env}`` dict.

    Same lifecycle as ``test_singlefile_proof._comparator_env``. Exposes the
    default (agent) sandbox -- where the submission tree is staged and tarred --
    plus the trusted ``comparator`` sandbox the checker uses. Per-test bring-up
    isolates an OOM/crash (and any compile-time tamper against the read-only
    rootfs) to a single case.
    """
    compose = str(get_compose_file(fc_commit(OEIS_DIR), literature=False))
    task_name = "pytest_lean_vuln_e2e"
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


async def _write_tree(env: SandboxEnvironment, files: dict[str, str]) -> None:
    """Stage ``files`` (paths relative to ``Submission/``) in the agent sandbox."""
    await env.exec(["rm", "-rf", SUBMISSION_DIR])
    await env.exec(["mkdir", "-p", SUBMISSION_DIR])
    for rel, content in files.items():
        await env.write_file(f"{SUBMISSION_DIR}/{rel}", content)


@pytest.mark.parametrize("case", _params())
async def test_scorer_verdict(case: Case, monkeypatch: pytest.MonkeyPatch) -> None:
    async with _sandboxes() as envs:
        agent_env = envs["default"]
        await _write_tree(agent_env, case.files)
        # The real scorer reads the tree from the agent (default) sandbox and
        # hands the tar to the checker, which verifies in the trusted
        # `comparator` sandbox. Point the scorer's `sandbox` at the agent env,
        # the checker's at the comparator env, and the store at the declared
        # claim.
        monkeypatch.setattr(scorer_mod, "sandbox", lambda *a, **k: agent_env)
        monkeypatch.setattr(checker_mod, "sandbox", lambda *a, **k: envs["comparator"])
        monkeypatch.setattr(scorer_mod, "store", lambda: _FakeStore(case.claim))

        state = TaskState(
            model=ModelName("mockllm/model"),
            sample_id=case.label,
            epoch=1,
            input=case.spec,
            messages=[],
            metadata={"sketch": case.spec, "decl_name": "tgt"},
        )
        score = await proof_scorer(SandboxComparator())(state, Target(""))

    assert score is not None
    accepted = score.value == CORRECT
    detail = (score.explanation or "")[-800:]
    assert accepted == case.secure_accept, (
        f"{case.label}: scorer {'ACCEPTED' if accepted else 'REJECTED'} but secure "
        f"behaviour is to {'ACCEPT' if case.secure_accept else 'REJECT'}.\n"
        f"stage={(score.metadata or {}).get('stage')}\n{detail}"
    )
