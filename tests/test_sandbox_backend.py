"""Tasks pick the sandbox config native to where they load: chart values inside
Kubernetes (Hawk), compose elsewhere. Fast, no docker."""

from pathlib import Path

import pytest
import yaml

import apn.task
from apn.dataset import ERDOS_DIR, fc_commit
from apn.task import get_sandbox_config, resolve_sandbox_backend


@pytest.fixture(autouse=True)
def sandbox_files_dir(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(apn.task, "SANDBOX_FILES_DIR", tmp_path)


def test_defaults_to_docker_outside_kubernetes(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delenv("KUBERNETES_SERVICE_HOST", raising=False)
    assert resolve_sandbox_backend(None) == "docker"


def test_defaults_to_k8s_inside_kubernetes(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("KUBERNETES_SERVICE_HOST", "10.100.0.1")
    assert resolve_sandbox_backend(None) == "k8s"


def test_explicit_backend_wins(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("KUBERNETES_SERVICE_HOST", "10.100.0.1")
    assert resolve_sandbox_backend("docker") == "docker"


def test_kubernetes_default_carries_values_only_settings(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The settings Hawk's compose conversion would drop reach the pods."""
    monkeypatch.setenv("KUBERNETES_SERVICE_HOST", "10.100.0.1")
    backend, path = get_sandbox_config(fc_commit(ERDOS_DIR), literature=True, backend=None)
    assert backend == "k8s"
    assert Path(path).name == "values.yaml"
    services = yaml.safe_load(Path(path).read_text())["services"]
    for name in ("default", "comparator"):
        assert "ephemeral-storage" in services[name]["resources"]["requests"]
    assert services["comparator"]["runtimeClassName"] == "CLUSTER_DEFAULT"
