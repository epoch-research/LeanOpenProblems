"""Inspect tasks for AlphaProof Nexus.

Run the basic agent over the bundled sketches with, e.g.::

    docker build -t apn-lean apn/lean
    inspect eval apn/task.py@apn_basic --model anthropic/claude-sonnet-4-6 \\
        -T num_subagents=4

The Lean sandbox image must be built first (see ``apn/lean/Dockerfile``).
"""

from __future__ import annotations

from pathlib import Path

from inspect_ai import Task, task

from apn.agents.basic import BasicAgentConfig, basic_agent
from apn.dataset import bundled_dataset, dataset_from_dir
from apn.scorer import proof_scorer
from apn.verifier.pantograph import PantographVerifier

COMPOSE_FILE = str(Path(__file__).parent / "lean" / "compose.yaml")


@task
def apn_basic(
    num_subagents: int = 4,
    max_episodes: int = 10,
    max_turns_per_episode: int = 40,
    max_edits_per_episode: int = 90,
    sketches_dir: str | None = None,
) -> Task:
    """The basic agent (A) over a directory of Lean sketches.

    Args:
        num_subagents: Independent prover subagents per problem (paper used up
            to 100).
        max_episodes: Ralph-loop episodes per subagent.
        max_turns_per_episode: LLM turns within an episode.
        max_edits_per_episode: ``search_replace`` edits allowed per episode.
        sketches_dir: Directory of ``*.lean`` sketches; defaults to the bundled
            smoke-test set.
    """
    verifier = PantographVerifier()
    config = BasicAgentConfig(
        num_subagents=num_subagents,
        max_episodes=max_episodes,
        max_turns_per_episode=max_turns_per_episode,
        max_edits_per_episode=max_edits_per_episode,
    )
    dataset = (
        dataset_from_dir(sketches_dir) if sketches_dir is not None else bundled_dataset()
    )
    return Task(
        dataset=dataset,
        solver=basic_agent(verifier, config),
        scorer=proof_scorer(verifier),
        sandbox=("docker", COMPOSE_FILE),
    )
