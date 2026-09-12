from __future__ import annotations

import os
import re
import tempfile
from pathlib import Path
from typing import Any

import yaml
from inspect_ai import Task, task

from apn import __version__
from apn.solver import AgentType, lean_prover
from apn.checker import SandboxComparator
from apn.dataset import (
    ERDOS_AUTOFORMALIZED_DIR,
    ERDOS_DIR,
    FC100_DIR,
    PERSONAL_CORRESP_DIR,
    OEIS_DIR,
    erdos_autoformalized_dataset,
    erdos_dataset,
    fc100open_dataset,
    fc_commit,
    fc_profile,
    load_subset,
    personal_corresp_dataset,
    oeis_dataset,
)
from apn.sandbox import SandboxBackend
from apn.scorer import proof_scorer

SANDBOX_FILES_DIR = Path(tempfile.gettempdir()) / "leanopenproblems_sandbox"
IMAGE_REPOSITORY_VAR = "LEAN_OPEN_PROBLEMS_IMAGE_NAME"
IMAGE_REPOSITORY_DEFAULT = "leanopenproblems"
# Compose interpolates ${VAR:-default} itself; the k8s values file is consumed
# verbatim by the Helm chart, so its writer resolves the variable at write time.
IMAGE_REPOSITORY = f"${{{IMAGE_REPOSITORY_VAR}:-{IMAGE_REPOSITORY_DEFAULT}}}"

# --------------------------------------------------------------------------- #
# Shared sandbox constants. Both backend writers draw from these so the two    #
# artifacts cannot drift semantically. Each config is written in its backend's #
# native vocabulary -- deliberately no compose->values conversion, even though #
# k8s_sandbox can auto-convert: the comparator `runtimeClassName` pin is the   #
# one line whose omission or mistranslation is *silently* unsound until        #
# https://github.com/leanprover/comparator/issues/83 lands upstream (gvisor    #
# has no Landlock, and comparator invokes landrun with --best-effort, which    #
# disables itself without error there), so it rides in the most direct         #
# representation available. Once comparator#83 is fixed a missing runtime      #
# fails loudly, and collapsing to a single compose file becomes a reasonable   #
# simplification.                                                              #
# --------------------------------------------------------------------------- #
AGENT_MEMORY_GIB = 32
COMPARATOR_MEMORY_GIB = 32


def _docker_tag_component(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]", "_", value)


def get_identifier_for_image(image_kind: str, fc_commit: str) -> str:
    """Image tag: keyed on apn.__version__ AND the FC pin, so datasets sharing
    a pin share images and a pin change alone yields fresh tags."""
    image_version = _docker_tag_component(__version__)
    return f"LeanOpenProblems_{image_kind}_{image_version}_fc_{fc_commit[:12]}"


def _agent_image_kind(literature: bool) -> str:
    return "agent_corpus" if literature else "agent"


def _build_section(target: str, fc_commit: str) -> dict[str, Any]:
    return {
        "context": str(Path(__file__).parent / "lean"),
        "target": target,
        "args": {"FC_COMMIT": fc_commit},
    }


def get_compose_file_content(fc_commit: str, literature: bool = False) -> str:
    """The docker-backend sandbox config (local runs, CI tests).

    Two services: the agent's workspace, and the trusted `comparator` verifier.
    The comparator container needs no filesystem hardening of its own
    (comparator-migration-plan.md §3.1): comparator's landrun (Landlock)
    sandbox confines the untrusted solution build to writes in `.lake`, every
    checker exec runs as the non-privileged user (`user=COMPARATOR_USER`; the
    image itself stays root for Inspect), and the checker's per-check
    reset-dotlake.sh restores a pristine `.lake`.
    """
    agent_kind = _agent_image_kind(literature)
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


def _image_repository() -> str:
    """The image repository, resolved at write time (Helm does not interpolate
    environment variables; compose does, hence the two spellings)."""
    return os.environ.get(IMAGE_REPOSITORY_VAR, IMAGE_REPOSITORY_DEFAULT)


def _k8s_resources(memory_gib: int) -> dict[str, Any]:
    """Just a memory limit: k8s defaults the request to the limit (so
    scheduling still reserves it), and CPU is compressible, so no CPU knobs."""
    return {"limits": {"memory": f"{memory_gib}Gi"}}


def get_values_file_content(fc_commit: str, literature: bool = False) -> str:
    """The k8s/Hawk-backend sandbox config: chart-native agent-env values.

    The agent sandbox only. Declares no ``comparator`` sandbox: on k8s the
    comparator is a separate, on-demand Helm release installed and uninstalled
    around each check.

    Note, the image repository is resolved at write time (Helm does not interpolate
    environment variables).
    """
    agent_kind = _agent_image_kind(literature)
    values: dict[str, Any] = {
        "services": {
            "default": {
                "image": f"{_image_repository()}:{get_identifier_for_image(agent_kind, fc_commit)}",
                "networkIsolated": True,
                "dnsRecord": True,
                "resources": _k8s_resources(AGENT_MEMORY_GIB),
            },
        }
    }
    return yaml.safe_dump(values, sort_keys=False)


def get_scoring_values_content(fc_commit: str) -> str:
    """The chart-native ``comparator`` service, for the on-demand scoring
    release.

    The comparator ``runtimeClassName`` pin must not ride through a translation
    layer while comparator#83 is open. A dropped or mistranslated pin lands that
    pod on gvisor, where landrun silently disables.
    """
    values: dict[str, Any] = {
        "services": {
            "default": {
                "image": f"{_image_repository()}:{get_identifier_for_image('comparator', fc_commit)}",
                # Dropping this pin lands the verifier on
                # gvisor, where landrun's Landlock syscalls do not exist and
                # comparator's --best-effort disables itself *without error*.
                # ``CLUSTER_DEFAULT`` is the chart's magic string for "do not set a
                # runtime class", i.e. the node's default runtime (runc).
                "runtimeClassName": "CLUSTER_DEFAULT",
                "networkIsolated": True,
                "dnsRecord": True,
                "resources": _k8s_resources(COMPARATOR_MEMORY_GIB),
            },
        }
    }
    return yaml.safe_dump(values, sort_keys=False)


def _config_dir(fc_commit: str, variant: str | None = None) -> Path:
    """Generated configs, isolated per (apn version, FC pin) and, for the
    per-task ones, per corpus variant, so they cannot clobber each other."""

    directory = (
        SANDBOX_FILES_DIR / _docker_tag_component(__version__) / f"fc_{fc_commit[:12]}"
    )
    if variant:
        directory = directory / variant
    directory.mkdir(parents=True, exist_ok=True)
    return directory


def _write_if_changed(path: Path, content: str) -> str:
    if not path.exists() or path.read_text() != content:
        path.write_text(content)
    return str(path)


def get_sandbox_config(
    fc_commit: str, literature: bool, backend: SandboxBackend
) -> tuple[str, str]:
    """The Inspect ``sandbox`` spec ``(type, config-file path)`` for a backend.

    Each backend gets its own generated artifact (``compose.yaml`` for docker,
    ``values.yaml`` for k8s -- k8s_sandbox treats any config file NOT named
    ``*compose.yaml``/``*compose.yml`` as chart values). Files are isolated in
    per-(version, FC pin, variant) subdirs so they don't clobber each other.
    """
    directory = _config_dir(fc_commit, "corpus" if literature else "closed-book")
    if backend == "docker":
        path = directory / "compose.yaml"
        content = get_compose_file_content(fc_commit, literature)
    elif backend == "k8s":
        path = directory / "values.yaml"
        content = get_values_file_content(fc_commit, literature)
    else:
        raise ValueError(
            f"Unknown sandbox_backend {backend!r}; expected 'docker' or 'k8s'."
        )
    return (backend, _write_if_changed(path, content))


def get_scoring_config(fc_commit: str) -> str:
    """Path to the scoring release's values file (k8s only).

    Keyed on (version, pin) but not the corpus variant -- the verifier image
    is the same either way. Named ``scoring-values.yaml``: anything ending in
    ``compose.yaml``/``compose.yml`` is parsed as compose by k8s_sandbox.
    """
    return _write_if_changed(
        _config_dir(fc_commit) / "scoring-values.yaml",
        get_scoring_values_content(fc_commit),
    )


def get_compose_file(fc_commit: str, literature: bool = False) -> Path:
    """The docker-backend compose file (kept for the test suites, which drive
    the docker sandbox lifecycle directly)."""
    return Path(get_sandbox_config(fc_commit, literature, "docker")[1])


def _comparator(fc_commit: str, backend: SandboxBackend) -> SandboxComparator:
    """The checker for a task, wired for its backend."""
    return SandboxComparator(
        backend=backend,
        scoring_values=get_scoring_config(fc_commit) if backend == "k8s" else None,
    )


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
        scorer=proof_scorer(_comparator(pin, sandbox_backend)),
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
        scorer=proof_scorer(_comparator(pin, sandbox_backend)),
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
        scorer=proof_scorer(_comparator(pin, sandbox_backend)),
        sandbox=get_sandbox_config(pin, literature, sandbox_backend),
    )


@task
def apn_erdos_autoformalized(
    subset: str | None = "bloom_selection",
    gated: bool = True,
    literature: bool = False,
    agent_type: AgentType = "react",
    sandbox_backend: SandboxBackend = "docker",
) -> Task:
    """The Erdős problems our own autoformalization pipeline formalized.

    The default ``bloom_selection`` subset applies Thomas Bloom's verdicts;
    ``subset=None`` runs the full manifest."""
    name_list = (
        load_subset(ERDOS_AUTOFORMALIZED_DIR, subset) if subset is not None else None
    )
    pin = fc_commit(ERDOS_AUTOFORMALIZED_DIR)
    return Task(
        dataset=erdos_autoformalized_dataset(names=name_list),
        solver=lean_prover(
            gated=gated,
            literature=literature,
            agent_type=agent_type,
            util_module=fc_profile(pin).util_module,
        ),
        scorer=proof_scorer(_comparator(pin, sandbox_backend)),
        sandbox=get_sandbox_config(pin, literature, sandbox_backend),
    )


@task
def apn_personal_corresp(
    subset: str | None = None,
    gated: bool = True,
    literature: bool = False,
    agent_type: AgentType = "react",
    sandbox_backend: SandboxBackend = "docker",
) -> Task:
    """Open conjectures sent to us in personal correspondence, formalized by
    their contributors (the finitistic dimension and Nakayama conjectures from
    Marczinzik–Böhmler; Šter's nilpotent-closure question via Pace Nielsen).
    No predefined subsets; the default runs the full manifest."""
    name_list = load_subset(PERSONAL_CORRESP_DIR, subset) if subset is not None else None
    pin = fc_commit(PERSONAL_CORRESP_DIR)
    return Task(
        dataset=personal_corresp_dataset(names=name_list),
        solver=lean_prover(
            gated=gated,
            literature=literature,
            agent_type=agent_type,
            util_module=fc_profile(pin).util_module,
        ),
        scorer=proof_scorer(SandboxComparator()),
        sandbox=get_sandbox_config(pin, literature, sandbox_backend),
    )
