"""The on-demand k8s scoring release.

On docker the comparator is a plain long-lived service in the compose file. On
k8s it is a Helm release of its own, installed around each check and uninstalled
afterwards -- a 32Gi pod idling for a 72h sample was most of a pod-lifetime of
reserved memory doing nothing.

A release we install ourselves does not go through Hawk's patching of
the sample's sandbox spec, so it would come up without the labels, annotations
and scheduling constraints Hawk writes into the agent release. The capture side
reads those back off the running agent sandbox at sample setup and carries an
allowlist of them onto the scoring release.

Note that in the case of a leaked sandbox (e.g. due to failed helm uninstall),
nothing cleans up the leak until after the eval finishes, which could be days.
"""

from __future__ import annotations

import logging
import os
import tempfile
import time
from collections.abc import AsyncIterator
from contextlib import asynccontextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Any, Literal

import anyio
import yaml
from inspect_ai.solver import Generate, Solver, TaskState, solver
from inspect_ai.util import SandboxEnvironment, StoreModel, sandbox
from tenacity import before_sleep_log, retry
from tenacity.retry import retry_if_exception_type
from tenacity.stop import stop_after_attempt
from tenacity.wait import wait_fixed, wait_random

if TYPE_CHECKING:
    from k8s_sandbox import K8sSandboxEnvironment, K8sSandboxEnvironmentConfig

logger = logging.getLogger(__name__)

SandboxBackend = Literal["docker", "k8s"]

FALLBACK_TASK_NAME = "apn_scoring"

_HELM_TIMEOUT_VAR = "INSPECT_HELM_UNINSTALL_TIMEOUT"
_HELM_TIMEOUT_DEFAULT_S = 600

_INSTALL_ATTEMPTS = 3
_INSTALL_BACKOFF_S = 10.0
_INSTALL_JITTER_S = 10.0


def _get_task_name() -> str:
    """The task name shows up in helm annotations and trace logs.
    Useful, but not the end of the world if we don't get it right."""

    try:
        # private Inspect API -- no public way to reach the active sample
        from inspect_ai.log._samples import sample_active

        active = sample_active()
        return active.task if active else FALLBACK_TASK_NAME
    except Exception:
        logger.warning("Could not read the active task name.", exc_info=True)
        return FALLBACK_TASK_NAME


class HawkSandboxValuesError(Exception):
    """The agent sandbox did not expose a readable Helm values file."""


@dataclass(frozen=True)
class HawkSandboxValues:
    """The allowlisted agent-release values the scoring release inherits.

    Hawk patches the release values via ``_patch_sample_sandbox`` function.
    However, the way we create the scoring sandbox does not go through that
    function. So, we grab some values from the default tool-use sandbox.

    Interesting values:

    - ``annotations`` -- mainly ``karpenter.sh/do-not-disrupt``, so the node
      cannot be consolidated out from under a check in progress.
    - ``labels`` -- the sample/task/job identifiers cost monitoring selects on,
      plus the Kueue queue and priority class the pod needs to be admitted.
    - ``coredns_image`` -- the chart injects a CoreDNS sidecar into every
      service pod unconditionally, and the chart's default image may not be
      pullable from an isolated cluster.
    - ``node_selector`` / ``tolerations`` -- the CPU architecture constraint
      and the arm64 taint toleration, without which the pod may not schedule.

    Deliberately not inherited: the agent's ``image``, ``command``,
    ``resources`` and ``runtimeClassName``;
    ``dnsRecord`` (the comparator needs no ClusterIP Service);
    ``additionalResources`` (on a human eval Hawk appends an SSH ingress policy
    selecting ``inspect/service: default``, and the comparator's own service is
    also named ``default``); and ``allowDomains``/``allowEntities``/
    ``allowCIDR`` (the comparator is network-isolated on purpose, and the
    red-team task's agent release deliberately has internet).

    Read at sample setup and merged straight into the scoring values file; only
    that file's path outlives the setup step.
    """

    annotations: dict[str, str]
    labels: dict[str, str]
    coredns_image: str | None
    node_selector: dict[str, str]
    tolerations: list[dict[str, Any]]


class ScoringRelease(StoreModel):
    """The merged Helm values the scoring release installs."""
    values: dict[str, Any] | None = None


def _read_hawk_sandbox_values(env: SandboxEnvironment) -> HawkSandboxValues:
    """Read the inheritable values off the default sandbox.

    Reaches through two private k8s_sandbox attributes -- there is no public
    way to ask a live sandbox what it was installed with, and the runner hands
    Inspect a rewritten temp file rather than the path the task declared, so
    re-reading the task's own file would miss every patch.

    Raises HawkSandboxValuesError if cannot load the config.
    """

    # Inspect hands out a SandboxEnvironmentProxy that records events; the
    # k8s_sandbox environment we want is its _sandbox.
    inner = getattr(env, "_sandbox", None)
    if isinstance(inner, SandboxEnvironment):
        env = inner

    config = getattr(env, "_config", None)
    if config is None:
        raise HawkSandboxValuesError(
            f"{type(env).__name__} exposes no _config; the private k8s_sandbox "
            "attribute this reads has probably moved."
        )
    values_path = getattr(config, "values", None)
    if values_path is None:
        raise HawkSandboxValuesError(
            "The agent sandbox config names no values file."
        )
    values = yaml.safe_load(Path(values_path).read_text())
    if not isinstance(values, dict):
        raise HawkSandboxValuesError(
            f"{values_path} parsed as {type(values).__name__}, not a mapping."
        )

    labels = values.get("labels") or {}
    if not labels:
        raise HawkSandboxValuesError(
            f"{values_path} carries no labels. Hawk stamps the sample, task "
            "and job identifiers plus the Kueue queue and priority class on "
            "every release, so an empty map means this is not the file the "
            "runner installed from."
        )
    annotations = values.get("annotations") or {}
    if not annotations:
        logger.warning(
            "%s carries no annotations; the scoring pod will install without "
            "karpenter.sh/do-not-disrupt and its node may be consolidated "
            "out from under a check in progress.",
            values_path,
        )

    services = values.get("services") or {}
    default = services.get("default") or {}
    return HawkSandboxValues(
        annotations=annotations,
        labels=labels,
        coredns_image=values.get("corednsImage"),
        node_selector=default.get("nodeSelector") or {},
        tolerations=default.get("tolerations") or [],
    )


@solver
def capture_hawk_sandbox_values(
    backend: SandboxBackend, base_values: dict[str, Any] | None = None
) -> Solver:
    """Merge the agent release's inheritable values into this sample's scoring
    values, and record them in the sample store.

    A task ``setup`` step rather than part of the agent solver, so that it fails
    at the start instead of at scoring time.

    A no-op on docker, where the comparator is a long-lived compose service and
    nobody installs a release.
    """

    if backend == "k8s" and base_values is None:
        raise ValueError("The k8s backend needs base_values to merge into.")

    async def solve(state: TaskState, generate: Generate) -> TaskState:
        if backend != "k8s":
            return state

        assert base_values is not None  # checked at construction
        hawk = _read_hawk_sandbox_values(sandbox())
        state.store_as(ScoringRelease).values = merged_scoring_values(
            base_values, hawk
        )
        return state

    return solve


def merged_scoring_values(
    base: dict[str, Any], hawk: HawkSandboxValues
) -> dict[str, Any]:
    """The scoring release's values: the static base, plus what we inherited.

    The base wins every collision. It is this eval's deliberate description of
    the verifier pod, and the agent release is only a source of cluster-side
    context.
    """

    values: dict[str, Any] = dict(base)
    services = dict(values.get("services") or {})
    default = dict(services.get("default") or {})

    values["annotations"] = {**hawk.annotations, **(values.get("annotations") or {})}
    values["labels"] = {
        **hawk.labels,
        **(values.get("labels") or {}),
    }
    if hawk.coredns_image and "corednsImage" not in values:
        values["corednsImage"] = hawk.coredns_image
    if hawk.node_selector:
        default["nodeSelector"] = {
            **hawk.node_selector,
            **(default.get("nodeSelector") or {}),
        }
    if hawk.tolerations:
        default["tolerations"] = [
            *hawk.tolerations,
            *(default.get("tolerations") or []),
        ]

    services["default"] = default
    values["services"] = services
    return values


@asynccontextmanager
async def k8s_scoring_env(
    values: dict[str, Any],
) -> AsyncIterator[SandboxEnvironment]:
    """Install a scoring release, yield its comparator sandbox, uninstall it.

    Inspect's own sandbox lifecycle offers no hook for additional sandboxes
    created mid-sample. Here we call ``sample_init``/``sample_cleanup`` on
    :class:`K8sSandboxEnvironment` directly. We have to make sure we clean
    things up, but in return we don't have a 32Gi pod sitting idle.

    ``values`` is the merged mapping. Helm only takes a file, so one is
    written for the duration of the release and removed with it. The suffix
    matters: k8s_sandbox parses anything named 
    ``*compose.yaml``/``*compose.yml`` as compose rather than chart values.
    """

    # Imported here, not at module scope: ``apn.checker`` imports this module
    # unconditionally, and a docker-backend run should not need
    # ``inspect-k8s-sandbox`` installed just to import the checker.
    from k8s_sandbox import K8sSandboxEnvironment, K8sSandboxEnvironmentConfig

    task_name = _get_task_name()
    with tempfile.TemporaryDirectory(prefix="apn-scoring-") as tmp:
        values_path = Path(tmp) / "scoring-values.yaml"
        values_path.write_text(yaml.safe_dump(values, sort_keys=False))
        config = K8sSandboxEnvironmentConfig(
            values=values_path,
            restarted_container_behavior="raise",
        )
        environments = await _install(K8sSandboxEnvironment, task_name, config)
        try:
            yield environments["default"]
        finally:
            await _cleanup(K8sSandboxEnvironment, task_name, config, environments)


@retry(
    stop=stop_after_attempt(_INSTALL_ATTEMPTS),
    wait=wait_fixed(_INSTALL_BACKOFF_S) + wait_random(0, _INSTALL_JITTER_S),
    # CancelledError is a BaseException, so this never swallows a cancel.
    retry=retry_if_exception_type(Exception),
    before_sleep=before_sleep_log(logger, logging.WARNING, exc_info=True),
    # Surface the helm failure itself rather than tenacity's RetryError.
    reraise=True,
)
async def _install(
    env_cls: type[K8sSandboxEnvironment],
    task_name: str,
    config: K8sSandboxEnvironmentConfig,
) -> dict[str, SandboxEnvironment]:
    """Install the scoring release, retrying a transient cluster failure.

    A cancelled sample still aborts at once: ``CancelledError`` is a
    ``BaseException``, so it is never caught here.

    A failed attempt may still leave a release behind, but it is tracked,
    so Inspect's end-of-task sweep uninstalls it.
    """

    started = time.monotonic()
    environments = await env_cls.sample_init(task_name, config, metadata={})
    logger.info(
        "Installed scoring sandbox release in %.1fs",
        time.monotonic() - started,
    )
    return environments


async def _cleanup(
    env_cls: type[K8sSandboxEnvironment],
    task_name: str,
    config: K8sSandboxEnvironmentConfig,
    environments: dict[str, SandboxEnvironment],
) -> None:
    """Uninstall the release, deleting the scoring pod."""

    try:
        # shield so a cancelled scoring pass still tears the pod down
        # but have a timeout so it doesn't hold forever
        # and make the timeout longer than what the helm uninstall timeout itself is
        with anyio.fail_after(
            float(os.environ.get(_HELM_TIMEOUT_VAR, _HELM_TIMEOUT_DEFAULT_S)) * 2,
            shield=True,
        ):
            # interrupted=True makes sample_cleanup a no-op, so always set False
            await env_cls.sample_cleanup(
                task_name, config, environments, interrupted=False
            )
    except Exception:
        # trap the exception so a failing helm uninstall doesn't change the checker response
        logger.exception("Failed to uninstall the scoring sandbox release.")
