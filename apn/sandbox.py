"""The on-demand k8s scoring release.

On docker the comparator is a plain long-lived service in the compose file. On
k8s it is a Helm release of its own, installed around each check and uninstalled
afterwards (:func:`k8s_scoring_env`) -- a 32Gi pod idling for a 72h sample was
most of a pod-lifetime of reserved memory doing nothing.

The values file that release renders is written by
:func:`apn.task.get_scoring_config`. This module holds no config writers; it
imports nothing from the rest of ``apn``, so ``apn.checker`` can reach the
runtime without an import cycle through ``apn.task``.
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

if TYPE_CHECKING:
    from k8s_sandbox import K8sSandboxEnvironment, K8sSandboxEnvironmentConfig

logger = logging.getLogger(__name__)

SandboxBackend = Literal["docker", "k8s"]

FALLBACK_TASK_NAME = "apn_scoring"

_HELM_TIMEOUT_VAR = "INSPECT_HELM_TIMEOUT"
_HELM_TIMEOUT_DEFAULT_S = 600

_INSTALL_ATTEMPTS = 3
_INSTALL_BACKOFF_S = 10


# ---------------------------------------------------------------------------- #
# Scoring-pod sizing caveats.                                                  #
#                                                                              #
# 1. Scoring pods are invisible to `max_sandboxes`. That limiter lives in      #
#    Inspect's `sandboxenv_context`, which wraps only the sample's *declared*  #
#    sandbox; `sample_init` never consults it. Peak concurrent pods can        #
#    therefore reach 2x the configured limit.                                  #
# 2. Scoring `exec`s share the single process-wide `PodOpExecutor` thread pool #
#    with every agent `exec`, and a slot is held for a command's full          #
#    duration. A 60-minute comparator run holds a slot for 60 minutes. Size    #
#    `INSPECT_MAX_POD_OPS` for both populations, not just the agent's.         #
# ---------------------------------------------------------------------------- #


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


async def _install(
    env_cls: type[K8sSandboxEnvironment],
    task_name: str,
    config: K8sSandboxEnvironmentConfig,
) -> dict[str, SandboxEnvironment]:
    """Install the scoring release, retrying a transient cluster failure.

    A cancelled sample still aborts at once: ``CancelledError`` is a
    ``BaseException``, so it is never caught here.

    A failed attempt may still have left a release behind -- ``sample_init``
    tracks it before running helm -- but it is tracked, so Inspect's
    end-of-task sweep uninstalls it.
    """

    for attempt in range(1, _INSTALL_ATTEMPTS + 1):
        started = time.monotonic()
        try:
            environments = await env_cls.sample_init(task_name, config, metadata={})
        except Exception:
            if attempt == _INSTALL_ATTEMPTS:
                raise
            logger.warning(
                "Scoring sandbox install failed (attempt %d/%d); retrying.",
                attempt,
                _INSTALL_ATTEMPTS,
                exc_info=True,
            )
            await anyio.sleep(_INSTALL_BACKOFF_S * attempt)
        else:
            logger.info(
                "Installed scoring sandbox release in %.1fs",
                time.monotonic() - started,
            )
            return environments

    raise AssertionError("unreachable: the last attempt returns or raises")


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
