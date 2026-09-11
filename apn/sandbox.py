"""The on-demand k8s scoring release.

On docker the comparator is a plain long-lived service in the compose file. On
k8s it is a Helm release of its own, installed around each check and uninstalled
afterwards (:func:`k8s_scoring_env`) -- a 32Gi pod idling for a 72h sample was
most of a pod-lifetime of reserved memory doing nothing.

Note that in the case of a leaked sandbox (e.g. due to failed helm uninstall),
nothing cleans up the leak until after the eval finishes, which could be days.
"""

from __future__ import annotations

import logging
import os
import time
from collections.abc import AsyncIterator
from contextlib import asynccontextmanager
from pathlib import Path
from typing import TYPE_CHECKING, Literal

import anyio
from inspect_ai.util import SandboxEnvironment
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


@asynccontextmanager
async def k8s_scoring_env(values_path: str) -> AsyncIterator[SandboxEnvironment]:
    """Install a scoring release, yield its comparator sandbox, uninstall it.

    Inspect's own sandbox lifecycle offers no hook for additional sandboxes
    created mid-sample. Here we call ``sample_init``/``sample_cleanup`` on
    :class:`K8sSandboxEnvironment` directly. We have to make sure we clean
    things up, but in return we don't have a 32Gi pod sitting idle.
    """

    # Imported here, not at module scope: ``apn.checker`` imports this module
    # unconditionally, and a docker-backend run should not need
    # ``inspect-k8s-sandbox`` installed just to import the checker.
    from k8s_sandbox import K8sSandboxEnvironment, K8sSandboxEnvironmentConfig

    task_name = _get_task_name()
    config = K8sSandboxEnvironmentConfig(values=Path(values_path).resolve())
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
