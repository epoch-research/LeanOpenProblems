"""Inspect task for AlphaProof Nexus (basic agent).

Build the Lean images, then run the agent over the bundled sketches::

    apn/lean/build.sh   # builds apn-lean-base, apn-agent, apn-scorer
    inspect eval apn/task.py@apn_basic --model anthropic/claude-sonnet-4-5

Run several independent attempts per problem with ``--epochs N`` (each epoch is a
fresh sample run with its own sandbox); pair it with an epoch reducer such as
``--epochs 4,pass_at_1`` if you want any-success scoring.
"""

from __future__ import annotations

from pathlib import Path

from inspect_ai import Task, task

from apn.agent import lean_prover
from apn.checker import SandboxSafeVerify
from apn.dataset import bundled_dataset, dataset_from_dir, oeis_dataset
from apn.scorer import proof_scorer
from apn.verifier.pantograph import PantographVerifier

COMPOSE_FILE = str(Path(__file__).parent / "lean" / "compose.yaml")
FC_COMPOSE_FILE = str(Path(__file__).parent / "lean" / "fc" / "compose.yaml")


@task
def apn_basic(sketches_dir: str | None = None) -> Task:
    """Prove Lean theorems with a ``deepagent`` against real Lean + Mathlib.

    Args:
        sketches_dir: Directory of ``*.lean`` files (each a theorem with a
            ``sorry`` proof); defaults to the bundled smoke-test set.
    """
    dataset = (
        dataset_from_dir(sketches_dir) if sketches_dir is not None else bundled_dataset()
    )
    return Task(
        dataset=dataset,
        # The agent works in the default sandbox (Pantograph, warm) for in-loop
        # compiler feedback; the scorer runs SafeVerify in a separate, trusted
        # "scorer" sandbox the agent never touches.
        solver=lean_prover(PantographVerifier()),
        scorer=proof_scorer(SandboxSafeVerify(sandbox_name="scorer")),
        sandbox=("docker", COMPOSE_FILE),
    )


@task
def apn_oeis(names: str | list[str] | None = None, gated: bool = False) -> Task:
    """Prove the autoformalized OEIS conjectures from the paper (44/492).

    Replicates the paper's OEIS evaluation: each sample is an autoformalized OEIS
    conjecture from Formal Conjectures (``OEIS/Auto``). The agent must discharge
    the embedded *test lemmas* (small-term checks guarding against
    misformalization) as well as the conjecture; SafeVerify then re-validates the
    whole file (every definition, test lemma, and the conjecture must be
    reproduced verbatim and proved sorry-free with only permitted axioms).

    Runs against the Formal Conjectures Lean v4.27 sandbox (build it first with
    ``apn/lean/fc/build.sh``).

    Args:
        names: Optional comma-separated list of conjecture theorem names to keep
            (a smoke subset); defaults to all 492.
        gated: If true, submissions are gated by SafeVerify -- a submission that
            fails verification is rejected and the agent must keep working (until
            a limit), and it is told only that verification failed (not why).
    """
    if names is None:
        name_list = None
    else:
        raw = names.split(",") if isinstance(names, str) else names
        name_list = [n.strip() for n in raw if n.strip()]
    # One checker instance drives both the submit gate (during the loop) and the
    # final scorer; both run in the trusted "scorer" sandbox.
    checker = SandboxSafeVerify(sandbox_name="scorer")
    return Task(
        dataset=oeis_dataset(names=name_list),
        solver=lean_prover(PantographVerifier(), gate=checker if gated else None),
        scorer=proof_scorer(checker),
        sandbox=("docker", FC_COMPOSE_FILE),
    )
