"""End-to-end Lean *soundness* tests, written from the agent's point of view.

Every case supplies **only the agent's ``Submission/`` file tree** (a ``{relative
path: contents}`` dict) plus the trusted target spec. The tree is written into the
live **agent** sandbox and scored by the **real** :func:`apn.scorer.proof_scorer`,
which tars it from that sandbox (``read_submission_tar``) and verifies it in the
**scorer** sandbox via :class:`~apn.checker.SandboxSafeVerify`. So each test
exercises the exact production path an agent submission travels -- nothing is
reimplemented, and the verdict is the one a real eval would record.

This is the security counterpart to ``test_singlefile_proof.py`` (which checks
plumbing/acceptance). Here we assert the *secure* verdict for a battery of
cheating attempts and honest baselines:

* **must REJECT** -- sorry/custom-axiom/native_decide (forbidden axioms), a
  weakened or missing target statement, an ``unsafe`` constant, an import-superset
  violation, and a kernel-bypassing constant injected into the *entry* module
  (caught by replay);
* **must REJECT -- any helper import.** The submission is compiled standalone, so
  an ``import Submission.…`` of a helper module does not resolve and the whole
  submission fails to compile (``compile_submission``). This closes what was once
  a soundness hole: safe_verify kernel-replays only the file it is handed and
  *trusts* an imported module's constants, so a kernel-invalid constant hidden in
  a helper (built by ``INJECT`` below) used to be accepted -- letting the agent
  prove ``False`` (hence anything) or "disprove" a true target. Now there is no
  way to import one, so these cases are ordinary regression guards: if a future
  change re-enables helper imports, they fail loudly;
* **must ACCEPT** -- honest single-file, definition reproduction, and a genuine
  disproof;
* **known vulnerability (xfail, strict)** -- *root code execution.* The
  submission is compiled (``lake env lean -o``) as root in the **same** sandbox
  that holds the trusted ``target.olean`` and the ``safe_verify`` binary, BEFORE
  ``safe_verify`` runs. A compile-time ``#eval`` of an IO action overwrites the
  ``safe_verify`` binary with a script that always exits 0, so a bogus proof
  (here ``sorry`` of a false target) is accepted. This documents the need for
  the separate-compilation-sandbox design -- compile the submission in an
  untrusted sandbox, run ``safe_verify`` in a trusted one whose TCB
  (target.olean + the verifier binary) is read-only / hash-pinned. The
  ``xfail(strict=True)`` case fails loudly (XPASS) the moment that lands -- the
  signal to delete the marker.

Memory: these deliberately import only ``Init`` (+ ``Lean`` where a metaprogram
needs it), not Mathlib, so safe_verify's footprint stays well under a modest
Docker memory limit. Docker is part of the test environment, so -- like the
sibling suite -- these always run; the first run builds the image, later runs hit
the layer cache.
"""

from __future__ import annotations

from contextlib import asynccontextmanager
from dataclasses import dataclass

import pytest

from inspect_ai.model import ModelName
from inspect_ai.scorer import CORRECT, Target
from inspect_ai.solver import TaskState
from inspect_ai.util._sandbox.context import (
    cleanup_sandbox_environments_sample,
    init_sandbox_environments_sample,
)
from inspect_ai.util._sandbox.docker.docker import DockerSandboxEnvironment

import apn.checker as checker_mod
import apn.scorer as scorer_mod
from apn.checker import SAFE_VERIFY_BIN, SandboxSafeVerify
from apn.layout import SUBMISSION_DIR
from apn.scorer import proof_scorer
from apn.task import get_compose_file

# --------------------------------------------------------------------------- #
# Building blocks for the submission trees.                                    #
# --------------------------------------------------------------------------- #
# Add `fakeFalse : False := True.intro` to the environment WITHOUT a kernel
# check (`debug.skipKernelTC` routes addDecl through addDeclWithoutChecking).
# The Declaration is built by hand so the *elaborator* never sees the type/value
# mismatch either. The result carries no axioms, so the transitive axiom guard
# does not catch it; only a kernel *replay* would -- which safe_verify does for
# the entry module but not for imported helpers. From any `False` you derive any
# false proposition via `.elim`.
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

# Root-code-execution attack on the scorer's TCB. The submission is *compiled*
# (`lake env lean -o`) as root in the SAME sandbox that holds the trusted
# target.olean and the safe_verify binary, BEFORE safe_verify runs. A `#eval` of
# an IO action runs at elaboration time, so it overwrites the safe_verify binary
# with a script that always exits 0 -- after which verification accepts anything.
# (writeFile preserves the existing exec bit; chmod is belt-and-braces.) Needs no
# import: IO.FS / IO.Process are in core (Init).
TAMPER_SAFE_VERIFY = (
    f'#eval (IO.FS.writeFile "{SAFE_VERIFY_BIN}" "#!/bin/sh\\nexit 0\\n" : IO Unit)\n'
    f'#eval (do let _ <- IO.Process.output '
    f'{{ cmd := "chmod", args := #["755", "{SAFE_VERIFY_BIN}"] }}; pure () : IO Unit)\n'
)


@dataclass(frozen=True)
class Case:
    label: str
    target: str
    files: dict[str, str]
    secure_accept: bool
    # Set for a confirmed-but-unfixed hole: the secure assertion is expected to
    # fail today, so the case is xfail(strict) and XPASSes -> fails once fixed.
    xfail_reason: str | None = None


CASES: list[Case] = [
    # ----------------------------- must REJECT ----------------------------- #
    Case(
        "entry_injection_caught_by_replay",
        "theorem tgt : False := by sorry\n",
        {"Spec.lean": INJECT + "\ntheorem tgt : False := fakeFalse\n"},
        secure_accept=False,
    ),
    Case(
        "sorry_in_entry",
        "theorem tgt : 2 + 2 = 4 := by sorry\n",
        {"Spec.lean": "theorem tgt : 2 + 2 = 4 := by sorry\n"},
        secure_accept=False,
    ),
    Case(
        "sorry_in_helper",
        "theorem tgt : 2 + 2 = 4 := by sorry\n",
        {
            "Helpers/Aux.lean": "theorem aux : 2 + 2 = 4 := by sorry\n",
            "Spec.lean": IMPORT_AUX + "theorem tgt : 2 + 2 = 4 := aux\n",
        },
        secure_accept=False,
    ),
    Case(
        "custom_axiom_in_helper",
        "theorem tgt : 2 + 2 = 4 := by sorry\n",
        {
            "Helpers/Aux.lean": "axiom bad : 2 + 2 = 4\ntheorem aux : 2 + 2 = 4 := bad\n",
            "Spec.lean": IMPORT_AUX + "theorem tgt : 2 + 2 = 4 := aux\n",
        },
        secure_accept=False,
    ),
    Case(
        "native_decide_forbidden_axiom",
        "theorem tgt : 2 + 2 = 4 := by sorry\n",
        {"Spec.lean": "theorem tgt : 2 + 2 = 4 := by native_decide\n"},
        secure_accept=False,
    ),
    Case(
        "weakened_statement",
        "theorem tgt : ∀ n : Nat, n + 0 = n := by sorry\n",
        {"Spec.lean": "theorem tgt : True := trivial\n"},
        secure_accept=False,
    ),
    Case(
        "missing_target_theorem",
        "theorem tgt : 2 + 2 = 4 := by sorry\n",
        {"Spec.lean": "theorem other : True := trivial\n"},
        secure_accept=False,
    ),
    Case(
        "unsafe_constant_in_entry",
        "theorem tgt : 2 + 2 = 4 := by sorry\n",
        {"Spec.lean": "unsafe def loop : Nat := loop\ntheorem tgt : 2 + 2 = 4 := by decide\n"},
        secure_accept=False,
    ),
    Case(
        "import_superset_violation",
        "import Lean\ntheorem tgt : True := by sorry\n",
        {"Spec.lean": "theorem tgt : True := trivial\n"},
        secure_accept=False,
    ),
    # ----------------------------- must ACCEPT ----------------------------- #
    Case(
        "honest_single_file",
        "theorem tgt : 2 + 2 = 4 := by sorry\n",
        {"Spec.lean": "theorem tgt : 2 + 2 = 4 := by decide\n"},
        secure_accept=True,
    ),
    Case(
        "honest_def_reproduction",
        "def foo : Nat := 7\ntheorem tgt : foo = 7 := by sorry\n",
        {"Spec.lean": "def foo : Nat := 7\ntheorem tgt : foo = 7 := by decide\n"},
        secure_accept=True,
    ),
    Case(
        "honest_disproof",
        "theorem tgt : 2 + 2 = 5 := by sorry\n",
        {"Spec.lean": "theorem tgt.disproof : 2 + 2 ≠ 5 := by decide\n"},
        secure_accept=True,
    ),
    # ------- helper injection: the closed hole, now must REJECT ------- #
    # Each injects a kernel-invalid `fakeFalse : False` into a helper and uses it
    # from the entry module. The submission is compiled standalone, so the
    # `import Submission.Helpers.Aux` fails to resolve and the whole thing is
    # rejected at compile_submission -- the injected helper is never even built.
    Case(
        "helper_inject_false_rejected",
        "theorem tgt : False := by sorry\n",
        {
            "Helpers/Aux.lean": INJECT,
            "Spec.lean": IMPORT_AUX + "theorem tgt : False := fakeFalse\n",
        },
        secure_accept=False,
    ),
    Case(
        "helper_inject_arith_rejected",
        "theorem tgt : 2 + 2 = 5 := by sorry\n",
        {
            "Helpers/Aux.lean": INJECT,
            "Spec.lean": IMPORT_AUX + "theorem tgt : 2 + 2 = 5 := fakeFalse.elim\n",
        },
        secure_accept=False,
    ),
    Case(
        "helper_inject_disproof_rejected",
        "theorem tgt : 2 + 2 = 4 := by sorry\n",
        {
            "Helpers/Aux.lean": INJECT,
            "Spec.lean": IMPORT_AUX + "theorem tgt.disproof : 2 + 2 ≠ 4 := fun _ => fakeFalse\n",
        },
        secure_accept=False,
    ),
    # ---- root code execution: TCB tamper during compile (xfail, strict) ---- #
    # The submission's compile-time #eval overwrites the safe_verify binary with
    # `exit 0`, so its `sorry` proof of the FALSE target 2+2=5 is accepted. The
    # secure verdict is REJECT (an intact verifier catches the sorryAx); the hole
    # makes it ACCEPT, so this is xfail(strict) until the separate-compilation
    # sandbox lands.
    Case(
        "root_exec_overwrites_safe_verify",
        "theorem tgt : 2 + 2 = 5 := by sorry\n",
        {"Spec.lean": TAMPER_SAFE_VERIFY + "theorem tgt : 2 + 2 = 5 := by sorry\n"},
        secure_accept=False,
        xfail_reason=(
            "root-code-exec hole: the submission is compiled as root in the same "
            "sandbox as the trusted target.olean + safe_verify binary, so a "
            "compile-time `#eval` overwrites safe_verify with `exit 0` and the "
            "bogus proof is accepted. Needs the separate-compilation-sandbox "
            "design (compile untrusted; verify in a trusted sandbox with a "
            "read-only / hash-pinned TCB). Delete this marker once that lands."
        ),
    ),
]


def _params() -> list:
    out = []
    for c in CASES:
        marks = (
            pytest.mark.xfail(strict=True, reason=c.xfail_reason)
            if c.xfail_reason
            else ()
        )
        out.append(pytest.param(c, id=c.label, marks=marks))
    return out


# --------------------------------------------------------------------------- #
# Harness: write the agent's tree into the live agent sandbox, run the real    #
# scorer (which verifies in the scorer sandbox).                               #
# --------------------------------------------------------------------------- #
@asynccontextmanager
async def _sandboxes():
    """Bring up the production compose; yield ``(agent_env, scorer_env)``.

    Same lifecycle as ``test_singlefile_proof._scorer_env`` but exposes both the
    default (agent) sandbox -- where the submission tree is staged and tarred --
    and the scorer sandbox where verification runs. Per-test bring-up isolates an
    OOM/crash to a single case.
    """
    compose = str(get_compose_file(literature=False))
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
            yield envs["default"], envs["scorer"]
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


async def _write_tree(env, files: dict[str, str]) -> None:
    """Stage ``files`` (paths relative to ``Submission/``) in the agent sandbox."""
    await env.exec(["rm", "-rf", SUBMISSION_DIR])
    await env.exec(["mkdir", "-p", SUBMISSION_DIR])
    for rel, content in files.items():
        await env.write_file(f"{SUBMISSION_DIR}/{rel}", content)


@pytest.mark.parametrize("case", _params())
async def test_scorer_verdict(case: Case, monkeypatch: pytest.MonkeyPatch) -> None:
    async with _sandboxes() as (agent_env, scorer_env):
        await _write_tree(agent_env, case.files)
        # The real scorer reads the tree from the agent (default) sandbox and
        # hands the tar to the checker, which builds/verifies in the scorer
        # sandbox. Point each module's `sandbox` at the matching live env.
        monkeypatch.setattr(scorer_mod, "sandbox", lambda *a, **k: agent_env)
        monkeypatch.setattr(checker_mod, "sandbox", lambda *a, **k: scorer_env)

        state = TaskState(
            model=ModelName("mockllm/model"),
            sample_id=case.label,
            epoch=1,
            input=case.target,
            messages=[],
            metadata={"sketch": case.target},
        )
        score = await proof_scorer(SandboxSafeVerify(sandbox_name="scorer"))(
            state, Target("")
        )

    accepted = score.value == CORRECT
    detail = (score.explanation or "")[-800:]
    assert accepted == case.secure_accept, (
        f"{case.label}: scorer {'ACCEPTED' if accepted else 'REJECTED'} but secure "
        f"behaviour is to {'ACCEPT' if case.secure_accept else 'REJECT'}.\n"
        f"stage={(score.metadata or {}).get('stage')}\n{detail}"
    )
