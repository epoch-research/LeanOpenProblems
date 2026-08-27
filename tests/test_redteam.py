"""Fast checks for the offline red-team task and its source setup."""

from __future__ import annotations

from pathlib import Path
from typing import Any, cast

import pytest
import yaml
from inspect_ai.util import SandboxEnvironmentSpec

from apn.redteam import (
    SOURCE_CHECKOUTS,
    apn_redteam_collatz,
)
from apn.task import SandboxBackend


@pytest.mark.parametrize("backend", ["docker", "k8s"])
def test_redteam_agent_uses_dedicated_offline_image(
    backend: SandboxBackend,
) -> None:
    task = apn_redteam_collatz(sandbox_backend=backend)
    sandbox_spec = task.sandbox
    assert isinstance(sandbox_spec, SandboxEnvironmentSpec)
    config_path = cast(str, sandbox_spec.config)
    config = cast(dict[str, Any], yaml.safe_load(Path(config_path).read_text()))
    services = cast(dict[str, dict[str, Any]], config["services"])

    assert task.setup is None
    assert set(services) == {"default", "comparator"}
    assert "LeanOpenProblems_redteam_" in services["default"]["image"]

    if backend == "docker":
        assert services["default"]["build"]["target"] == "redteam"
        assert services["default"]["network_mode"] == "none"
        assert services["comparator"]["network_mode"] == "none"
    else:
        assert services["default"]["networkIsolated"] is True
        assert services["comparator"]["networkIsolated"] is True
        assert "allowEntities" not in config


def test_redteam_image_bakes_the_scored_source_revisions() -> None:
    dockerfile = (Path(__file__).parents[1] / "apn" / "lean" / "Dockerfile").read_text()
    checkouts = {
        directory: revision
        for directory, _repo, revision, _role in SOURCE_CHECKOUTS
    }

    assert f"ARG COMPARATOR_COMMIT={checkouts['comparator']}" in dockerfile
    assert f"ARG LEAN4EXPORT_COMMIT={checkouts['lean4export']}" in dockerfile
    assert f"ARG LANDRUN_COMMIT={checkouts['landrun']}" in dockerfile
    assert f"ARG LEAN4_PROJECT_COMMIT={checkouts['lean4-project']}" in dockerfile
    assert f"ARG LEAN4_COMPARATOR_COMMIT={checkouts['lean4-comparator']}" in dockerfile
    assert checkouts["lean4-project"] == "db93fe1608548721853390a10cd40580fe7d22ae"
    assert checkouts["lean4-comparator"] == "6a10ac8c22beadecabdbb0919c2b50214762f91d"
    assert all(len(revision) == 40 for revision in checkouts.values())
