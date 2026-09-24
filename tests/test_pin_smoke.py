"""Per-pin contract: each registered FC pin's production images build, and
Comparator in them accepts an honest proof and an honest disproof and rejects
a ``sorry``. The pins come from ``apn.dataset.FC_PINS`` (the ``every_pin``
fixture), so a new pin is covered without any CI change; Comparator's verdict
logic itself is pin-invariant and is exercised by the other comparator suites
at one pin."""

from __future__ import annotations

from collections.abc import AsyncIterator

import pytest
import pytest_asyncio
from inspect_ai.util import SandboxEnvironment

import apn.checker as checker_mod
from apn.checker import Claim, CheckOutcome, SandboxComparator
from apn.dataset import fc_profile
from apn.filetree import read_submission_tar
from tests.lean_sandbox import production_envs, write_submission


@pytest_asyncio.fixture(loop_scope="module", scope="module")
async def envs(every_pin: str) -> AsyncIterator[dict[str, SandboxEnvironment]]:
    async with production_envs("pytest_pin_smoke", every_pin) as envs:
        yield envs


def _spec(pin: str, body: str, proof: str, disproof: str) -> str:
    return (
        f"import {fc_profile(pin).util_module}\n"
        f"theorem tgt : {body} := {proof}\n"
        f"theorem tgt.disproof : ¬ (type_of% @tgt) := {disproof}\n"
    )


async def _check(
    envs: dict[str, SandboxEnvironment],
    monkeypatch: pytest.MonkeyPatch,
    spec: str,
    submission: str,
    claim: Claim,
) -> CheckOutcome:
    await write_submission(envs["default"], {"Spec.lean": submission})
    tar = await read_submission_tar(envs["default"])
    monkeypatch.setattr(checker_mod, "sandbox", lambda *a, **k: envs["comparator"])
    return await SandboxComparator().check(spec, tar, decl="tgt", claim=claim)


@pytest.mark.asyncio(loop_scope="module")
async def test_honest_proof_is_accepted(
    envs: dict[str, SandboxEnvironment], every_pin: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    spec = _spec(every_pin, "1 + 1 = 2", "by sorry", "sorry")
    submission = _spec(every_pin, "1 + 1 = 2", "by norm_num", "sorry")
    outcome = await _check(envs, monkeypatch, spec, submission, "proof")
    assert outcome.ok, f"expected acceptance, got stage={outcome.stage}:\n{outcome.detail[-1500:]}"


@pytest.mark.asyncio(loop_scope="module")
async def test_honest_disproof_is_accepted(
    envs: dict[str, SandboxEnvironment], every_pin: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    spec = _spec(every_pin, "1 + 1 = 3", "by sorry", "sorry")
    submission = _spec(every_pin, "1 + 1 = 3", "by sorry", "by norm_num")
    outcome = await _check(envs, monkeypatch, spec, submission, "disproof")
    assert outcome.ok, f"expected acceptance, got stage={outcome.stage}:\n{outcome.detail[-1500:]}"


@pytest.mark.asyncio(loop_scope="module")
async def test_sorry_is_rejected(
    envs: dict[str, SandboxEnvironment], every_pin: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    spec = _spec(every_pin, "1 + 1 = 2", "by sorry", "sorry")
    outcome = await _check(envs, monkeypatch, spec, spec, "proof")
    assert not outcome.ok
    assert outcome.stage == "comparator"
