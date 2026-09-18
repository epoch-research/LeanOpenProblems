"""Tests for the values the on-demand k8s scoring release installs with.

A release we install ourselves never passes through Hawk's
``_patch_sample_sandbox``, so the labels, annotations and scheduling
constraints the runner stamps on the agent release would be missing from the
verifier pod. ``capture_hawk_sandbox_values`` runs as the task's ``setup``
step, reads an allowlist of those off the live agent sandbox, merges them into
this eval's own static values and parks the result in the sample store, where
the checker picks it up at scoring time.

Three seams, tested separately: reading (``_read_hawk_sandbox_values``, which
reaches through two private k8s_sandbox attributes and so is the part most
likely to rot), merging (``merged_scoring_values``) and the solver that joins
them. Hand-rolled fakes, no mock library, as in test_checker.py.
"""

from __future__ import annotations

import logging
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest
import yaml
from inspect_ai.model import ModelName
from inspect_ai.solver import TaskState
from inspect_ai.util import SandboxEnvironment
from inspect_ai.util._sandbox.events import SandboxEnvironmentProxy

import apn.sandbox as sandbox_mod
from apn.sandbox import (
    HawkSandboxValues,
    HawkSandboxValuesError,
    ScoringRelease,
    capture_hawk_sandbox_values,
    merged_scoring_values,
)

# A plausible post-patch agent values file: what Hawk writes, reduced to the
# keys the capture either inherits or deliberately drops.
HAWK_VALUES: dict[str, Any] = {
    "annotations": {"karpenter.sh/do-not-disrupt": "true"},
    "labels": {
        "inspect/sample-id": "A000045",
        "kueue.x-k8s.io/queue-name": "eval-queue",
    },
    "corednsImage": "registry.internal/coredns:1.11",
    "allowEntities": ["world"],
    "services": {
        "default": {
            "image": "agent:latest",
            "nodeSelector": {"kubernetes.io/arch": "arm64"},
            "tolerations": [{"key": "arm64", "operator": "Exists"}],
        }
    },
}

BASE: dict[str, Any] = {
    "services": {"default": {"image": "comparator:pinned", "runtimeClassName": None}}
}


def _write(tmp_path: Path, values: dict[str, Any]) -> Path:
    path = tmp_path / "agent-values.yaml"
    path.write_text(yaml.safe_dump(values))
    return path


def _env(values_path: Path | None) -> Any:
    """A stand-in for the live K8sSandboxEnvironment the capture reads."""
    return SimpleNamespace(_config=SimpleNamespace(values=values_path))


def _bare_env() -> Any:
    """A sandbox with no ``_config`` at all."""
    return SimpleNamespace()


class _FakeK8sEnv(SandboxEnvironment):
    """Enough of a real SandboxEnvironment to survive being proxied."""

    def __init__(self, values_path: Path) -> None:
        self._config = SimpleNamespace(values=values_path)

    async def exec(self, *args: Any, **kwargs: Any) -> Any:
        raise NotImplementedError

    async def write_file(self, *args: Any, **kwargs: Any) -> None:
        raise NotImplementedError

    async def read_file(self, *args: Any, **kwargs: Any) -> Any:
        raise NotImplementedError

    @classmethod
    async def sample_cleanup(cls, *args: Any, **kwargs: Any) -> None:
        raise NotImplementedError


def _proxied_env(values_path: Path) -> Any:
    """What ``sandbox()`` actually hands back: the environment behind the
    event-recording proxy Inspect wraps it in."""
    return SandboxEnvironmentProxy(_FakeK8sEnv(values_path))


# --- reading the agent release's values -------------------------------------


def test_reads_the_allowlisted_values(tmp_path: Path) -> None:
    hawk = sandbox_mod._read_hawk_sandbox_values(_env(_write(tmp_path, HAWK_VALUES)))

    assert hawk == HawkSandboxValues(
        annotations={"karpenter.sh/do-not-disrupt": "true"},
        labels={
            "inspect/sample-id": "A000045",
            "kueue.x-k8s.io/queue-name": "eval-queue",
        },
        coredns_image="registry.internal/coredns:1.11",
        node_selector={"kubernetes.io/arch": "arm64"},
        tolerations=[{"key": "arm64", "operator": "Exists"}],
    )


def test_agent_image_and_network_are_not_inherited(tmp_path: Path) -> None:
    # The red-team task's agent release has internet on purpose; the verifier
    # must not ride along on it, nor come up running the agent's image.
    hawk = sandbox_mod._read_hawk_sandbox_values(_env(_write(tmp_path, HAWK_VALUES)))

    inherited = merged_scoring_values(BASE, hawk)
    assert "allowEntities" not in inherited
    assert inherited["services"]["default"]["image"] == "comparator:pinned"


def test_reads_through_the_event_proxy(tmp_path: Path) -> None:
    # sandbox() returns a SandboxEnvironmentProxy, not the k8s environment
    # itself, and the proxy carries no _config of its own.
    hawk = sandbox_mod._read_hawk_sandbox_values(
        _proxied_env(_write(tmp_path, HAWK_VALUES))
    )

    assert hawk.labels == HAWK_VALUES["labels"]
    assert hawk.node_selector == {"kubernetes.io/arch": "arm64"}


def test_missing_private_config_is_reported() -> None:
    # The whole read hangs off two private k8s_sandbox attributes; when one
    # moves, the eval should say so rather than silently install a bare pod.
    with pytest.raises(HawkSandboxValuesError, match="_config"):
        sandbox_mod._read_hawk_sandbox_values(_bare_env())


def test_config_without_a_values_file_is_reported() -> None:
    with pytest.raises(HawkSandboxValuesError, match="no values file"):
        sandbox_mod._read_hawk_sandbox_values(_env(None))


def test_non_mapping_values_file_is_reported(tmp_path: Path) -> None:
    path = tmp_path / "agent-values.yaml"
    path.write_text("- just\n- a list\n")

    with pytest.raises(HawkSandboxValuesError, match="not a mapping"):
        sandbox_mod._read_hawk_sandbox_values(_env(path))


def test_missing_labels_is_reported(tmp_path: Path) -> None:
    # Hawk stamps labels on every release, so a file without them is not the
    # file the runner installed from -- most likely the task's own template.
    values = {k: v for k, v in HAWK_VALUES.items() if k != "labels"}

    with pytest.raises(HawkSandboxValuesError, match="no labels"):
        sandbox_mod._read_hawk_sandbox_values(_env(_write(tmp_path, values)))


def test_missing_annotations_warns_but_proceeds(
    tmp_path: Path, caplog: pytest.LogCaptureFixture
) -> None:
    # Losing karpenter.sh/do-not-disrupt only risks the node being consolidated
    # mid-check, which is not worth failing the sample over.
    values = {k: v for k, v in HAWK_VALUES.items() if k != "annotations"}

    with caplog.at_level(logging.WARNING, logger=sandbox_mod.__name__):
        hawk = sandbox_mod._read_hawk_sandbox_values(_env(_write(tmp_path, values)))

    assert hawk.annotations == {}
    assert "do-not-disrupt" in caplog.text


def test_absent_scheduling_constraints_read_as_empty(tmp_path: Path) -> None:
    values = {"labels": HAWK_VALUES["labels"], "annotations": HAWK_VALUES["annotations"]}

    hawk = sandbox_mod._read_hawk_sandbox_values(_env(_write(tmp_path, values)))

    assert hawk.coredns_image is None
    assert hawk.node_selector == {}
    assert hawk.tolerations == []


# --- merging ----------------------------------------------------------------


HAWK = HawkSandboxValues(
    annotations={"karpenter.sh/do-not-disrupt": "true"},
    labels={"inspect/sample-id": "A000045"},
    coredns_image="registry.internal/coredns:1.11",
    node_selector={"kubernetes.io/arch": "arm64"},
    tolerations=[{"key": "arm64", "operator": "Exists"}],
)


def test_merge_carries_the_cluster_side_context() -> None:
    values = merged_scoring_values(BASE, HAWK)

    assert values["annotations"] == {"karpenter.sh/do-not-disrupt": "true"}
    assert values["labels"] == {"inspect/sample-id": "A000045"}
    assert values["corednsImage"] == "registry.internal/coredns:1.11"
    default = values["services"]["default"]
    assert default["nodeSelector"] == {"kubernetes.io/arch": "arm64"}
    assert default["tolerations"] == [{"key": "arm64", "operator": "Exists"}]


def test_base_wins_every_collision() -> None:
    # The base is this eval's deliberate description of the verifier pod; the
    # agent release is only a source of cluster context.
    base: dict[str, Any] = {
        "annotations": {"karpenter.sh/do-not-disrupt": "false"},
        "labels": {"inspect/sample-id": "ours"},
        "corednsImage": "pinned/coredns:1.12",
        "services": {
            "default": {"nodeSelector": {"kubernetes.io/arch": "amd64"}},
        },
    }

    values = merged_scoring_values(base, HAWK)

    assert values["annotations"]["karpenter.sh/do-not-disrupt"] == "false"
    assert values["labels"]["inspect/sample-id"] == "ours"
    assert values["corednsImage"] == "pinned/coredns:1.12"
    assert values["services"]["default"]["nodeSelector"] == {
        "kubernetes.io/arch": "amd64"
    }


def test_merge_does_not_mutate_the_base() -> None:
    # The base comes from get_scoring_values and is merged once per sample.
    base = {"services": {"default": {"image": "comparator:pinned"}}}
    before = yaml.safe_dump(base)

    merged_scoring_values(base, HAWK)

    assert yaml.safe_dump(base) == before


def test_merge_with_nothing_inherited_is_the_base() -> None:
    empty = HawkSandboxValues(
        annotations={}, labels={}, coredns_image=None, node_selector={}, tolerations=[]
    )

    values = merged_scoring_values(BASE, empty)

    assert values["services"]["default"]["image"] == "comparator:pinned"
    assert values["annotations"] == {}
    assert "corednsImage" not in values


# --- the setup solver -------------------------------------------------------


def _state() -> TaskState:
    return TaskState(
        model=ModelName("mockllm/model"),
        sample_id="A000045",
        epoch=1,
        input="",
        messages=[],
    )


def test_k8s_without_base_values_fails_at_construction() -> None:
    # At task build time, not at scoring time hours into a sample.
    with pytest.raises(ValueError, match="base_values"):
        capture_hawk_sandbox_values("k8s")


async def test_setup_stores_the_merged_values(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    env = _env(_write(tmp_path, HAWK_VALUES))
    monkeypatch.setattr(sandbox_mod, "sandbox", lambda *a, **k: env)
    state = _state()

    await capture_hawk_sandbox_values("k8s", BASE)(state, None)  # type: ignore[arg-type]

    values = state.store_as(ScoringRelease).values
    assert values is not None
    assert values["labels"]["inspect/sample-id"] == "A000045"
    assert values["services"]["default"]["image"] == "comparator:pinned"


async def test_docker_setup_is_a_no_op(monkeypatch: pytest.MonkeyPatch) -> None:
    # Nobody installs a release on docker, and the capture must not touch the
    # compose sandbox looking for a values file that does not exist.
    def _boom(*args: Any, **kwargs: Any) -> Any:
        raise AssertionError("docker setup must not read the sandbox")

    monkeypatch.setattr(sandbox_mod, "sandbox", _boom)
    state = _state()

    await capture_hawk_sandbox_values("docker")(state, None)  # type: ignore[arg-type]

    assert state.store_as(ScoringRelease).values is None


async def test_setup_propagates_a_read_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Fail the sample at setup rather than let it run for hours and then find
    # it cannot score.
    monkeypatch.setattr(sandbox_mod, "sandbox", lambda *a, **k: _bare_env())

    with pytest.raises(HawkSandboxValuesError):
        await capture_hawk_sandbox_values("k8s", BASE)(_state(), None)  # type: ignore[arg-type]
