from __future__ import annotations

import os
import re
import tempfile
from pathlib import Path
from typing import Any, Literal

import yaml
from inspect_ai import Task, task

from apn import __version__
from apn.solver import AgentType, lean_prover
from apn.checker import SandboxComparator
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

SANDBOX_FILES_DIR = Path(tempfile.gettempdir()) / "leanopenproblems_sandbox"
IMAGE_REPOSITORY_VAR = "LEAN_OPEN_PROBLEMS_IMAGE_NAME"
IMAGE_REPOSITORY_DEFAULT = "leanopenproblems"
# Compose interpolates ${VAR:-default} itself; the k8s values file is consumed
# verbatim by the Helm chart, so its writer resolves the variable at write time.
IMAGE_REPOSITORY = f"${{{IMAGE_REPOSITORY_VAR}:-{IMAGE_REPOSITORY_DEFAULT}}}"

SandboxBackend = Literal["docker", "k8s"]

# --------------------------------------------------------------------------- #
# Shared sandbox constants. Both backend writers draw from these so the two    #
# artifacts cannot drift semantically. Each config is written in its backend's #
# native vocabulary -- deliberately no compose->values conversion, even though #
# k8s_sandbox can auto-convert: the k8s `runtimeClassName` pin is the one line #
# whose omission or mistranslation is *silently* unsound until                 #
# https://github.com/leanprover/comparator/issues/83 lands upstream (gvisor    #
# has no Landlock, and comparator invokes landrun with --best-effort, which    #
# disables itself without error there), so it rides in the most direct         #
# representation available. Once comparator#83 is fixed a missing runtime      #
# fails loudly, and collapsing to a single compose file becomes a reasonable   #
# simplification.                                                              #
# --------------------------------------------------------------------------- #
AGENT_MEMORY_GIB = 10
# Comparator holds both text exports in memory and replays the solution's
# closure through its kernel; 16 GiB is the §7 starting point (the DAG-shaped
# export removes SafeVerify's rebuildExpr blowup).
COMPARATOR_MEMORY_GIB = 16


def _docker_tag_component(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]", "_", value)


def get_identifier_for_image(image_kind: str, fc_commit: str) -> str:
    """Image tag: keyed on apn.__version__ AND the FC pin, so datasets sharing
    a pin share images and a pin change alone yields fresh tags."""
    image_version = _docker_tag_component(__version__)
    return f"LeanOpenProblems_{image_kind}_{image_version}_fc_{fc_commit[:12]}"


def _agent_image_kind(literature: bool, override: str | None = None) -> str:
    return override if override is not None else ("agent_corpus" if literature else "agent")


def _build_section(target: str, fc_commit: str) -> dict[str, Any]:
    return {
        "context": str(Path(__file__).parent / "lean"),
        "target": target,
        "args": {"FC_COMMIT": fc_commit},
    }


def get_compose_file_content(
    fc_commit: str,
    literature: bool = False,
    agent_image_kind: str | None = None,
) -> str:
    """The docker-backend sandbox config (local runs, CI tests).

    Two services: the agent's workspace, and the trusted `comparator` verifier.
    The comparator container needs no filesystem hardening of its own
    (comparator-migration-plan.md §3.1): comparator's landrun (Landlock)
    sandbox confines the untrusted solution build to writes in `.lake`, the
    image runs as a non-privileged user, and the checker's per-check
    reset-dotlake.sh restores a pristine `.lake`.
    """
    agent_kind = _agent_image_kind(literature, agent_image_kind)
    compose: dict[str, Any] = {
        "services": {
            "default": {
                "image": f"{IMAGE_REPOSITORY}:{get_identifier_for_image(agent_kind, fc_commit)}",
                "build": _build_section(agent_kind, fc_commit),
                "init": True,
                "entrypoint": "tail -f /dev/null",
                "mem_limit": f"{AGENT_MEMORY_GIB}g",
                "network_mode": "none",
            },
            "comparator": {
                "image": f"{IMAGE_REPOSITORY}:{get_identifier_for_image('comparator', fc_commit)}",
                "build": _build_section("comparator", fc_commit),
                "init": True,
                "entrypoint": "tail -f /dev/null",
                "mem_limit": f"{COMPARATOR_MEMORY_GIB}g",
                "network_mode": "none",
            },
        }
    }
    return yaml.safe_dump(compose, sort_keys=False)


def get_values_file_content(
    fc_commit: str,
    literature: bool = False,
    agent_image_kind: str | None = None,
) -> str:
    """The k8s/Hawk-backend sandbox config: chart-native agent-env values.

    Written directly in the Helm chart's vocabulary. k8s_sandbox could
    auto-convert the compose file, but the ``runtimeClassName`` pin must not
    ride through a translation layer while comparator#83 is open: a dropped or
    mistranslated pin lands pods on gvisor, where landrun silently disables
    (first note below). Notes:

    - ``runtimeClassName: CLUSTER_DEFAULT`` is the chart's magic string for
      "do not set a runtime class": pods run under the node's default runtime
      (runc), where landrun's Landlock syscalls exist. Without the pin the
      chart defaults to gvisor, whose sentry does not implement Landlock --
      and until comparator#83 lands upstream that failure is *silent*, so this
      eval must not run under gvisor/`isolation: strict` (plan §7.6).
    - The image repository is resolved at write time (Helm does not
      interpolate environment variables).
    """
    repository = os.environ.get(IMAGE_REPOSITORY_VAR, IMAGE_REPOSITORY_DEFAULT)
    agent_kind = _agent_image_kind(literature, agent_image_kind)

    # Just a memory limit: k8s defaults the request to the limit (so
    # scheduling still reserves it), and CPU is compressible, so no CPU knobs.
    def resources(memory_gib: int) -> dict[str, Any]:
        return {"limits": {"memory": f"{memory_gib}Gi"}}

    values: dict[str, Any] = {
        "services": {
            "default": {
                "image": f"{repository}:{get_identifier_for_image(agent_kind, fc_commit)}",
                "runtimeClassName": "CLUSTER_DEFAULT",
                "networkIsolated": True,
                "dnsRecord": True,
                "resources": resources(AGENT_MEMORY_GIB),
            },
            "comparator": {
                "image": f"{repository}:{get_identifier_for_image('comparator', fc_commit)}",
                "runtimeClassName": "CLUSTER_DEFAULT",
                "networkIsolated": True,
                "dnsRecord": True,
                "resources": resources(COMPARATOR_MEMORY_GIB),
            },
        }
    }
    return yaml.safe_dump(values, sort_keys=False)


def get_sandbox_config(
    fc_commit: str,
    literature: bool,
    backend: SandboxBackend,
    agent_image_kind: str | None = None,
) -> tuple[str, str]:
    """The Inspect ``sandbox`` spec ``(type, config-file path)`` for a backend.

    Each backend gets its own generated artifact (``compose.yaml`` for docker,
    ``values.yaml`` for k8s -- k8s_sandbox treats any config file NOT named
    ``*compose.yaml``/``*compose.yml`` as chart values). Files are isolated in
    per-(version, FC pin, variant) subdirs so they don't clobber each other.
    """
    variant = (
        _docker_tag_component(agent_image_kind)
        if agent_image_kind is not None
        else ("corpus" if literature else "closed-book")
    )
    directory = (
        SANDBOX_FILES_DIR
        / _docker_tag_component(__version__)
        / f"fc_{fc_commit[:12]}"
        / variant
    )
    directory.mkdir(parents=True, exist_ok=True)
    if backend == "docker":
        path = directory / "compose.yaml"
        content = get_compose_file_content(fc_commit, literature, agent_image_kind)
    elif backend == "k8s":
        path = directory / "values.yaml"
        content = get_values_file_content(fc_commit, literature, agent_image_kind)
    else:
        raise ValueError(f"Unknown sandbox_backend {backend!r}; expected 'docker' or 'k8s'.")
    if not path.exists() or path.read_text() != content:
        path.write_text(content)
    return (backend, str(path))


def get_compose_file(fc_commit: str, literature: bool = False) -> Path:
    """The docker-backend compose file (kept for the test suites, which drive
    the docker sandbox lifecycle directly)."""
    return Path(get_sandbox_config(fc_commit, literature, "docker")[1])


@task
def apn_oeis(
    subset: str | None = None,
    gated: bool = True,
    literature: bool = False,
    agent_type: AgentType = "react",
    sandbox_backend: SandboxBackend = "docker",
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
        scorer=proof_scorer(SandboxComparator()),
        sandbox=get_sandbox_config(pin, literature, sandbox_backend),
    )


@task
def apn_fc100open(
    subset: str | None = None,
    gated: bool = True,
    literature: bool = False,
    agent_type: AgentType = "react",
    sandbox_backend: SandboxBackend = "docker",
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
        scorer=proof_scorer(SandboxComparator()),
        sandbox=get_sandbox_config(pin, literature, sandbox_backend),
    )


@task
def apn_erdos(
    subset: str | None = "bloom_selection",
    gated: bool = True,
    literature: bool = False,
    agent_type: AgentType = "react",
    sandbox_backend: SandboxBackend = "docker",
) -> Task:
    """The Bloom statement selection of Erdős problems."""
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
        scorer=proof_scorer(SandboxComparator()),
        sandbox=get_sandbox_config(pin, literature, sandbox_backend),
    )
