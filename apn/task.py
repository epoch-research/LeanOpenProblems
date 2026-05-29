"""Inspect tasks for AlphaProof Nexus.

Run the basic agent over the bundled sketches with, e.g.::

    docker build -t apn-lean apn/lean
    inspect eval apn/task.py@apn_basic --model anthropic/claude-sonnet-4-5 \\
        -T num_subagents=2

The Lean sandbox image must be built first (see ``apn/lean/Dockerfile``). Each
subagent gets its own Lean sandbox, so ``num_subagents`` containers are started
per problem -- keep it small locally, as each loads Mathlib.
"""

from __future__ import annotations

import tempfile
from pathlib import Path
from typing import Any

import yaml

from inspect_ai import Task, task

from apn.agents.basic import BasicAgentConfig, basic_agent
from apn.dataset import bundled_dataset, dataset_from_dir
from apn.scorer import proof_scorer
from apn.verifier.pantograph import PantographVerifier

LEAN_IMAGE = "apn-lean"


def _generate_compose(num_subagents: int, image: str = LEAN_IMAGE) -> str:
    """Write a Docker compose file with one Lean service per subagent.

    Each service uses the prebuilt local image (``x-local`` so Inspect does not
    try to pull it) and has no network (the warm Pantograph daemon is local to
    the container). Returns the path to the generated file.
    """
    services: dict[str, Any] = {}
    for i in range(max(1, num_subagents)):
        service: dict[str, Any] = {
            "image": image,
            "command": ["sleep", "infinity"],
            "init": True,
            "x-local": True,
            "network_mode": "none",
        }
        if i == 0:
            service["x-default"] = True
        services[f"agent{i}"] = service

    handle = tempfile.NamedTemporaryFile(
        mode="w", suffix=".yaml", prefix="apn_compose_", delete=False
    )
    with handle:
        yaml.safe_dump({"services": services}, handle, sort_keys=False)
    return handle.name


@task
def apn_basic(
    num_subagents: int = 2,
    max_episodes: int = 10,
    max_turns_per_episode: int = 40,
    sketches_dir: str | None = None,
) -> Task:
    """The basic agent (A) over a directory of Lean sketches.

    Args:
        num_subagents: Independent prover subagents per problem, each with its
            own Lean sandbox (paper used up to 100). Kept small by default
            because every subagent starts a container.
        max_episodes: Ralph-loop episodes per subagent.
        max_turns_per_episode: LLM turns within an episode.
        sketches_dir: Directory of ``*.lean`` sketches; defaults to the bundled
            smoke-test set.
    """
    verifier = PantographVerifier()
    config = BasicAgentConfig(
        num_subagents=num_subagents,
        max_episodes=max_episodes,
        max_turns_per_episode=max_turns_per_episode,
    )
    dataset = (
        dataset_from_dir(sketches_dir) if sketches_dir is not None else bundled_dataset()
    )
    return Task(
        dataset=dataset,
        solver=basic_agent(verifier, config),
        scorer=proof_scorer(verifier),
        sandbox=("docker", _generate_compose(num_subagents)),
    )
