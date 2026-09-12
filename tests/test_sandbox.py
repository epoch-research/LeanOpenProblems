"""Lifecycle tests for the on-demand k8s scoring sandbox.

``k8s_scoring_env`` owns a Helm release's whole life: install, hand the
comparator environment to the checker, uninstall. The invariant worth testing
is the teardown side. A leaked 32Gi pod has no timely collector (Inspect sweeps
at eval end; the Hawk janitor waits an hour past a terminal runner Job), so
cleanup must survive the body raising *and* the sample being cancelled -- while
a cleanup failure must never replace the verdict or exception the checker was
already carrying.

``k8s_scoring_env`` imports k8s_sandbox in its own body, so a docker-only
install need not have the package to import ``apn.checker``. That import reads
the two names off ``k8s_sandbox`` at call time, so the fixture patches them
there. Same hand-rolled-fake style as test_checker.py: no mock library.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any

import anyio
import pytest

from apn.sandbox import (
    _INSTALL_ATTEMPTS,
    FALLBACK_TASK_NAME,
    k8s_scoring_env,
)


class FakeConfig:
    def __init__(self, values: Path) -> None:
        self.values = values


class FakeEnv:
    """Stands in for a K8sSandboxEnvironment (the checker only ever execs)."""

    def __init__(self, name: str) -> None:
        self.name = name


class FakeK8sSandboxEnvironment:
    """Records every sample_init/sample_cleanup call the helper makes.

    An instance, not a class, even though the real ``sample_init`` is a
    classmethod. ``apn.sandbox`` only looks the two methods up on the patched
    name and passes it around as a value, so bound instance methods serve --
    and each test gets a fresh call log instead of a hand-written reset.
    """

    def __init__(self) -> None:
        self.init_calls: list[tuple[str, FakeConfig, dict[str, str]]] = []
        self.cleanup_calls: list[tuple[str, dict[str, Any]]] = []
        self.cleanup_error: Exception | None = None
        # The first `init_failures` sample_init calls raise `init_error`.
        self.init_error: Exception | None = None
        self.init_failures = 0
        # `default` first, exactly as the real sample_init reorders it -- so a
        # test that picks the first environment instead of indexing by name
        # fails.
        self.services: tuple[str, ...] = ("default", )

    async def sample_init(
        self, task_name: str, config: FakeConfig, metadata: dict[str, str]
    ) -> dict[str, Any]:
        self.init_calls.append((task_name, config, metadata))
        if self.init_error is not None and len(self.init_calls) <= self.init_failures:
            raise self.init_error
        return {name: FakeEnv(name) for name in self.services}

    async def sample_cleanup(
        self,
        task_name: str,
        config: FakeConfig,
        environments: dict[str, Any],
        interrupted: bool,
    ) -> None:
        self.cleanup_calls.append((task_name, environments))
        if self.cleanup_error is not None:
            raise self.cleanup_error


@pytest.fixture
def fake_k8s(monkeypatch: pytest.MonkeyPatch) -> FakeK8sSandboxEnvironment:
    fake = FakeK8sSandboxEnvironment()
    monkeypatch.setattr("k8s_sandbox.K8sSandboxEnvironment", fake)
    monkeypatch.setattr("k8s_sandbox.K8sSandboxEnvironmentConfig", FakeConfig)
    return fake


async def test_installs_yields_comparator_and_uninstalls(
    fake_k8s: FakeK8sSandboxEnvironment, tmp_path: Path
) -> None:
    values = tmp_path / "scoring-values.yaml"
    values.write_text("services: {}\n")

    async with k8s_scoring_env(str(values)) as env:
        # By name, not the first entry: `default` is deliberately first above.
        assert env.name == "default"  # type: ignore[attr-defined]
        assert len(fake_k8s.init_calls) == 1
        assert fake_k8s.cleanup_calls == []

    assert len(fake_k8s.cleanup_calls) == 1


async def test_body_exception_still_uninstalls_and_propagates(
    fake_k8s: FakeK8sSandboxEnvironment, tmp_path: Path
) -> None:
    values = tmp_path / "scoring-values.yaml"
    values.write_text("services: {}\n")

    with pytest.raises(RuntimeError, match="reset failed"):
        async with k8s_scoring_env(str(values)):
            raise RuntimeError(".lake reset failed")

    assert len(fake_k8s.cleanup_calls) == 1


async def test_cancellation_still_uninstalls(
    fake_k8s: FakeK8sSandboxEnvironment, tmp_path: Path
) -> None:
    values = tmp_path / "scoring-values.yaml"
    values.write_text("services: {}\n")

    with anyio.move_on_after(0.01):
        async with k8s_scoring_env(str(values)):
            await anyio.sleep(30)

    assert len(fake_k8s.cleanup_calls) == 1


async def test_failed_uninstall_is_swallowed(
    fake_k8s: FakeK8sSandboxEnvironment, tmp_path: Path
) -> None:
    # A helm hiccup must not replace the checker's verdict.
    fake_k8s.cleanup_error = RuntimeError("helm uninstall exploded")
    values = tmp_path / "scoring-values.yaml"
    values.write_text("services: {}\n")

    async with k8s_scoring_env(str(values)) as env:
        verdict = f"checked in {env.name}"  # type: ignore[attr-defined]

    assert verdict == "checked in default"


async def test_failed_uninstall_preserves_the_body_exception(
    fake_k8s: FakeK8sSandboxEnvironment, tmp_path: Path
) -> None:
    fake_k8s.cleanup_error = RuntimeError("helm uninstall exploded")
    values = tmp_path / "scoring-values.yaml"
    values.write_text("services: {}\n")

    with pytest.raises(RuntimeError, match="reset failed"):
        async with k8s_scoring_env(str(values)):
            raise RuntimeError(".lake reset failed")


async def test_release_is_named_for_the_active_sample(
    fake_k8s: FakeK8sSandboxEnvironment,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from types import SimpleNamespace

    import inspect_ai.log._samples as samples_mod

    active = SimpleNamespace(
        task="apn_oeis",
        sample=SimpleNamespace(id="A000045", metadata={"decl_name": "fib_thm"}),
    )
    monkeypatch.setattr(samples_mod, "sample_active", lambda: active)
    values = tmp_path / "scoring-values.yaml"
    values.write_text("services: {}\n")

    async with k8s_scoring_env(str(values)):
        pass

    (task_name, _, metadata) = fake_k8s.init_calls[0]
    assert task_name == "apn_oeis"
    # The release only needs a name; the sample's own metadata is not forwarded.
    assert metadata == {}


async def test_falls_back_when_no_sample_is_active(
    fake_k8s: FakeK8sSandboxEnvironment, tmp_path: Path
) -> None:
    values = tmp_path / "scoring-values.yaml"
    values.write_text("services: {}\n")

    async with k8s_scoring_env(str(values)):
        pass

    (task_name, _, metadata) = fake_k8s.init_calls[0]
    assert task_name == FALLBACK_TASK_NAME
    assert metadata == {}


async def test_failed_install_is_retried(
    fake_k8s: FakeK8sSandboxEnvironment,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr("apn.sandbox._INSTALL_BACKOFF_S", 0)
    fake_k8s.init_error = RuntimeError("helm install exploded")
    fake_k8s.init_failures = 1
    values = tmp_path / "scoring-values.yaml"
    values.write_text("services: {}\n")

    async with k8s_scoring_env(str(values)) as env:
        assert env.name == "default"  # type: ignore[attr-defined]

    assert len(fake_k8s.init_calls) == 2
    assert len(fake_k8s.cleanup_calls) == 1


async def test_install_gives_up_after_the_last_attempt(
    fake_k8s: FakeK8sSandboxEnvironment,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr("apn.sandbox._INSTALL_BACKOFF_S", 0)
    fake_k8s.init_error = RuntimeError("helm install exploded")
    fake_k8s.init_failures = _INSTALL_ATTEMPTS
    values = tmp_path / "scoring-values.yaml"
    values.write_text("services: {}\n")

    with pytest.raises(RuntimeError, match="helm install exploded"):
        async with k8s_scoring_env(str(values)):
            pass

    assert len(fake_k8s.init_calls) == _INSTALL_ATTEMPTS
    # sample_init never handed back an environment, so there is nothing this
    # helper can clean up; the half-installed release (if any) stays tracked by
    # k8s_sandbox for the end-of-task sweep.
    assert fake_k8s.cleanup_calls == []
