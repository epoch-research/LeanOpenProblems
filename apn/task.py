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
from apn.dataset import bundled_dataset, dataset_from_dir
from apn.scorer import proof_scorer
from apn.verifier.pantograph import PantographVerifier

COMPOSE_FILE = str(Path(__file__).parent / "lean" / "compose.yaml")


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
