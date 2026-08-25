from __future__ import annotations

import re
import tempfile
from pathlib import Path

from inspect_ai import Task, task

from apn import __version__
from apn.solver import AgentType, lean_prover
from apn.checker import SandboxSafeVerify
from apn.dataset import (
    ERDOS_DIR,
    FC100_DIR,
    OEIS_DIR,
    erdos_dataset,
    fc100open_dataset,
    fc_commit,
    fc_profile,
    load_subset,
    oeis_dataset,
)
from apn.scorer import proof_scorer

COMPOSE_FILES_DIR = Path(tempfile.gettempdir()) / "leanopenproblems_compose"
IMAGE_REPOSITORY = "${LEAN_OPEN_PROBLEMS_IMAGE_NAME:-leanopenproblems}"


def _docker_tag_component(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]", "_", value)


def get_identifier_for_image(image_kind: str, fc_commit: str) -> str:
    """Image tag: keyed on apn.__version__ AND the FC pin, so datasets sharing
    a pin share images and a pin change alone yields fresh tags."""
    image_version = _docker_tag_component(__version__)
    return f"LeanOpenProblems_{image_kind}_{image_version}_fc_{fc_commit[:12]}"


def _build_section(target: str, fc_commit: str) -> str:
    return f"""\
    build:
      context: {Path(__file__).parent / "lean"}
      target: {target}
      args:
        FC_COMMIT: {fc_commit}
"""


def get_compose_file_content(fc_commit: str, literature: bool = False) -> str:
    agent_kind = "agent_corpus" if literature else "agent"
    agent_tag = get_identifier_for_image(agent_kind, fc_commit)
    scorer_tag = get_identifier_for_image("scorer", fc_commit)
    return f"""
services:
  default:
    image: {IMAGE_REPOSITORY}:{agent_tag}
{_build_section(agent_kind, fc_commit)}    init: true
    entrypoint: tail -f /dev/null
    mem_limit: 10g
    network_mode: none
  compile:
    image: {IMAGE_REPOSITORY}:{scorer_tag}
{_build_section("scorer", fc_commit)}    init: true
    entrypoint: tail -f /dev/null
    mem_limit: 10g
    network_mode: none
  scorer:
    image: {IMAGE_REPOSITORY}:{scorer_tag}
{_build_section("scorer", fc_commit)}    init: true
    entrypoint: tail -f /dev/null
    mem_limit: 50g
    network_mode: none
"""


def get_compose_file(fc_commit: str, literature: bool = False) -> Path:
    # Both variants are named compose.yaml, isolated in per-(FC pin, variant)
    # subdirs so they don't clobber each other.
    # k8s_sandbox only treats a sandbox config as a compose file when its name *ends* in
    # "compose.yaml"/"compose.yml" (is_docker_compose_file); anything else
    # would be fed to the agent-env Helm chart verbatim.
    variant = "corpus" if literature else "closed-book"
    compose_path = (
        COMPOSE_FILES_DIR
        / _docker_tag_component(__version__)
        / f"fc_{fc_commit[:12]}"
        / variant
        / "compose.yaml"
    )
    compose_path.parent.mkdir(parents=True, exist_ok=True)
    content = get_compose_file_content(fc_commit, literature)
    if not compose_path.exists() or compose_path.read_text() != content:
        compose_path.write_text(content)
    return compose_path


@task
def apn_oeis(
    subset: str | None = None,
    gated: bool = True,
    literature: bool = False,
    agent_type: AgentType = "react",
) -> Task:
    """The Formal Conjectures autoformalized OEIS conjectures (492 samples).

    Predefined subsets (``apn/data/oeis/subsets/``): ``lite`` (a seeded random
    100 for cheaper sweeps), ``tsoukalas_proved_38``/``tsoukalas_unproved_40``
    (the AlphaProof Nexus paper's published outcomes).
    """
    name_list = load_subset(OEIS_DIR, subset) if subset is not None else None
    pin = fc_commit(OEIS_DIR)

    return Task(
        dataset=oeis_dataset(names=name_list),
        solver=lean_prover(
            gated=gated,
            literature=literature,
            agent_type=agent_type,
            util_module=fc_profile(pin).util_module,
        ),
        scorer=proof_scorer(SandboxSafeVerify(sandbox_name="scorer")),
        sandbox=("docker", str(get_compose_file(pin, literature))),
    )


@task
def apn_fc100open(
    subset: str | None = None,
    gated: bool = True,
    literature: bool = False,
    agent_type: AgentType = "react",
) -> Task:
    name_list = load_subset(FC100_DIR, subset) if subset is not None else None
    pin = fc_commit(FC100_DIR)
    return Task(
        dataset=fc100open_dataset(names=name_list),
        solver=lean_prover(
            gated=gated,
            literature=literature,
            agent_type=agent_type,
            util_module=fc_profile(pin).util_module,
        ),
        scorer=proof_scorer(SandboxSafeVerify(sandbox_name="scorer")),
        sandbox=("docker", str(get_compose_file(pin, literature))),
    )


@task
def apn_erdos(
    subset: str | None = "bloom_selection",
    gated: bool = True,
    literature: bool = False,
    agent_type: AgentType = "react",
) -> Task:
    """The Bloom statement selection of Erdős problems.

    Thomas Bloom selected 70 Erdős problem numbers for review; 48 have
    formalized statements in formal-conjectures, and the review picked one
    representative statement per problem (see
    ``apn/data/erdos/ERDOS_PROBLEM_STATEMENT_SELECTION.md`` and
    ``NOTICE.md``). Statement text is FC at the dataset's pin
    (``apn/data/erdos/fc_commit``) -- the exact commit the sandbox images
    bake, certified statement-identical to the review commit -- and every
    ``answer(...) ↔`` form is certified-rewritten to the binary task, plain
    ``P`` (recorded ``True``/``False`` verdicts un-filled, and FC's
    recorded-verdict annotations stripped, so the answer key cannot leak).

    Bare ``apn_erdos`` runs the default ``bloom_selection`` subset: the 47
    scoreable selected statements (problem 508's ``HadwigerNelsonProblem`` is
    value-typed and excluded). ``subset=None`` runs the whole census instead
    -- every non-excluded research statement of the 48 vendored files,
    research-category variants included.
    """
    name_list = load_subset(ERDOS_DIR, subset) if subset is not None else None
    pin = fc_commit(ERDOS_DIR)
    return Task(
        dataset=erdos_dataset(names=name_list),
        solver=lean_prover(
            gated=gated,
            literature=literature,
            agent_type=agent_type,
            util_module=fc_profile(pin).util_module,
        ),
        scorer=proof_scorer(SandboxSafeVerify(sandbox_name="scorer")),
        sandbox=("docker", str(get_compose_file(pin, literature))),
    )
