"""Tasks pick the sandbox config native to where they load: chart values in a
Hawk runner, compose elsewhere. Fast, no docker."""

from pathlib import Path

import pytest
import yaml

import apn.task
from apn.dataset import ERDOS_DIR, fc_commit
from apn.task import SandboxBackend, get_sandbox_config, resolve_sandbox_backend


@pytest.fixture(autouse=True)
def sandbox_files_dir(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(apn.task, "SANDBOX_FILES_DIR", tmp_path)


def test_defaults_to_docker_outside_hawk(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delenv("HAWK_JOB_ID", raising=False)
    assert resolve_sandbox_backend(None) == "docker"


def test_defaults_to_k8s_in_hawk_runner(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("HAWK_JOB_ID", "bloom68-alv3junt54xqrybd")
    assert resolve_sandbox_backend(None) == "k8s"


def test_explicit_backend_wins(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("HAWK_JOB_ID", "bloom68-alv3junt54xqrybd")
    assert resolve_sandbox_backend("docker") == "docker"


def test_hawk_default_carries_values_only_settings(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The settings Hawk's compose conversion would drop reach the pods."""
    monkeypatch.setenv("HAWK_JOB_ID", "bloom68-alv3junt54xqrybd")
    backend, path = get_sandbox_config(fc_commit(ERDOS_DIR), literature=True, backend=None)
    assert backend == "k8s"
    assert Path(path).name == "values.yaml"
    services = yaml.safe_load(Path(path).read_text())["services"]
    for name in ("default", "comparator"):
        assert "ephemeral-storage" in services[name]["resources"]["requests"]
    assert services["comparator"]["runtimeClassName"] == "CLUSTER_DEFAULT"


@pytest.mark.parametrize("backend", ["docker", "k8s"])
def test_swarm_members_share_the_agent_sandbox(backend: SandboxBackend) -> None:
    _, path = get_sandbox_config(
        fc_commit(ERDOS_DIR),
        literature=False,
        backend=backend,
        members=["prover-1", "prover-2"],
    )
    services = yaml.safe_load(Path(path).read_text())["services"]
    assert list(services) == ["default", "comparator-prover-1", "comparator-prover-2"]
    memory = (
        services["default"]["mem_limit"]
        if backend == "docker"
        else services["default"]["resources"]["limits"]["memory"]
    )
    assert memory.rstrip("Gig") == str(apn.task.SWARM_AGENT_MEMORY_GIB)
