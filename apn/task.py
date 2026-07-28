from __future__ import annotations

import re
import tempfile
from pathlib import Path

from inspect_ai import Task, task

from apn import __version__
from apn.solver import AgentType, lean_prover
from apn.checker import SandboxSafeVerify
from apn.dataset import (
    ERDOS_SUBSETS_DIR,
    FC100_SUBSETS_DIR,
    erdos_dataset,
    fc100open_dataset,
    load_subset,
    oeis_dataset,
)
from apn.scorer import proof_scorer

COMPOSE_FILES_DIR = Path(tempfile.gettempdir()) / "leanopenproblems_compose"
IMAGE_REPOSITORY = "${LEAN_OPEN_PROBLEMS_IMAGE_NAME:-leanopenproblems}"


def _docker_tag_component(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]", "_", value)


def get_identifier_for_image(image_kind: str) -> str:
    image_version = _docker_tag_component(__version__)
    return f"LeanOpenProblems_{image_kind}_{image_version}"


def _build_section(target: str) -> str:
    return f"""\
    build:
      context: {Path(__file__).parent / "lean"}
      target: {target}
"""


def get_compose_file_content(literature: bool = False) -> str:
    agent_kind = "agent_corpus" if literature else "agent"
    agent_tag = get_identifier_for_image(agent_kind)
    scorer_tag = get_identifier_for_image("scorer")
    return f"""
services:
  default:
    image: {IMAGE_REPOSITORY}:{agent_tag}
{_build_section(agent_kind)}    init: true
    entrypoint: tail -f /dev/null
    mem_limit: 10g
    network_mode: none
  compile:
    image: {IMAGE_REPOSITORY}:{scorer_tag}
{_build_section("scorer")}    init: true
    entrypoint: tail -f /dev/null
    mem_limit: 10g
    network_mode: none
  scorer:
    image: {IMAGE_REPOSITORY}:{scorer_tag}
{_build_section("scorer")}    init: true
    entrypoint: tail -f /dev/null
    mem_limit: 50g
    network_mode: none
"""


def get_compose_file(literature: bool = False) -> Path:
    # Both variants are named compose.yaml, isolated in per-variant subdirs so they
    # don't clobber each other.
    # k8s_sandbox only treats a sandbox config as a compose file when its name *ends* in
    # "compose.yaml"/"compose.yml" (is_docker_compose_file); anything else
    # would be fed to the agent-env Helm chart verbatim.
    variant = "corpus" if literature else "closed-book"
    compose_path = (
        COMPOSE_FILES_DIR / _docker_tag_component(__version__) / variant / "compose.yaml"
    )
    compose_path.parent.mkdir(parents=True, exist_ok=True)
    content = get_compose_file_content(literature)
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
    name_list = load_subset(subset) if subset is not None else None

    return Task(
        dataset=oeis_dataset(names=name_list),
        solver=lean_prover(
            # An effectively infinite max_attempts on the built-in Inspect react() and deepagent()
            # solvers is used to implement "gated submission".
            # This is a bit of a hack: it would be clearer to implement this inside the solver.
            # However, doing it like this lets us benefit automatically from upstream improvements
            # in the built-in solvers; in particular, Inspect maintainers will keep these up to date
            # with internal Inspect changes.
            max_attempts=99_999_999 if gated else 1,
            literature=literature,
            agent_type=agent_type,
        ),
        scorer=proof_scorer(SandboxSafeVerify(sandbox_name="scorer")),
        sandbox=("docker", str(get_compose_file(literature))),
    )


@task
def apn_fc100open(
    subset: str | None = None,
    gated: bool = True,
    literature: bool = False,
    agent_type: AgentType = "react",
) -> Task:
    name_list = load_subset(subset, FC100_SUBSETS_DIR) if subset is not None else None
    return Task(
        dataset=fc100open_dataset(names=name_list),
        solver=lean_prover(
            max_attempts=99_999_999 if gated else 1,
            literature=literature,
            agent_type=agent_type,
        ),
        scorer=proof_scorer(SandboxSafeVerify(sandbox_name="scorer")),
        sandbox=("docker", str(get_compose_file(literature))),
    )


@task
def apn_erdos(
    subset: str | None = None,
    gated: bool = True,
    literature: bool = False,
    agent_type: AgentType = "react",
) -> Task:
    """The Tsoukalas paper's canonical Erdős attempted set (arXiv 2605.22763).

    All 353 FC ErdosProblems statements the paper's agent attempted, of which
    350 ship as samples (3 have no statement at the vendored FC commit; see
    ``apn/data/erdos/EXCLUDED.txt``). Statement text is FC at 67338a1 -- the
    exact commit the sandbox images bake -- and every ``answer(...) ↔`` form is
    certified-rewritten to the attempt-time binary task, plain ``P`` (recorded
    ``True``/``False`` verdicts un-filled, and FC's recorded-verdict
    annotations stripped, so the answer key cannot leak). No predefined
    subsets are shipped; run ad-hoc slices via ``--sample-id``.
    """
    name_list = load_subset(subset, ERDOS_SUBSETS_DIR) if subset is not None else None
    return Task(
        dataset=erdos_dataset(names=name_list),
        solver=lean_prover(
            max_attempts=99_999_999 if gated else 1,
            literature=literature,
            agent_type=agent_type,
        ),
        scorer=proof_scorer(SandboxSafeVerify(sandbox_name="scorer")),
        sandbox=("docker", str(get_compose_file(literature))),
    )
