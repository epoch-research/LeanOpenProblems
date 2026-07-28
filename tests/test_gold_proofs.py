"""End-to-end regression: the paper's published gold proofs verify CORRECT.

The repo vendors the AlphaProof Nexus paper's solved proofs under
``tests/data/gold_proofs/`` -- one complete, ``sorry``-free Lean proof per
conjecture in the ``tsoukalas_proved_38`` subset (committed copies of the upstream
``reference_sources/.../APNOutputs/OEIS`` files, which are gitignored and absent
in CI; see that dir's README). This test runs each of them through the *real*
:class:`apn.checker.SandboxSafeVerify` against the live ``scorer`` sandbox -- the
exact scoring path an eval uses -- and asserts the verdict is accepted. For each
conjecture:

* **target** = our committed ``apn/data/oeis/Isolated/<stem>.lean`` spec. This is
  the dataset's single source for ``metadata["sketch"]``, i.e. precisely the text
  the scorer compiles as the trusted target at eval time (a leading license
  comment never reaches the olean, so reading the file directly is verification-
  equivalent to going through the dataset).
* **submission** = the gold proof file, packed as ``Submission/Spec.lean``, with
  its ``target_theorem_0`` renamed to the spec's own theorem name. The paper
  names every challenge theorem ``target_theorem_0``; our specs name it after the
  conjecture, and ``safe_verify`` matches each target declaration against the
  submission by *exact name*. A real agent keeps the spec's name, so the renamed
  gold file is exactly the submission a perfect agent would produce.

This is the complement of every other checker test. Those prove ``safe_verify``
says **no** to bad proofs (a ``sorry``/custom axiom/compile failure is rejected --
``test_singlefile_proof.py``, ``test_checker.py``) and that our isolated
statements line up with the published ones (the ``test_oeis_isolation.py``
oracle). This proves it says **yes** to the known-good proofs, end to end. It is
the only test that catches the over-strict-checker class: an axiom-allowlist
regression, a break in the module-name flip, a Mathlib/toolchain skew, or a
``def``-value mismatch between our spec and the gold proof -- any of which would
silently reject valid proofs and tank the benchmark with every rejection test
still green.

The ``scorer`` sandbox is brought up **once for the whole module** through
Inspect's lifecycle from the production compose (``apn.task.get_compose_file``,
which builds from ``apn/lean/Dockerfile``), exactly like
``tests/test_singlefile_proof.py``, and every conjecture is a parametrized async
case that reuses it. This matters for two reasons: ``safe_verify`` materializes
the full Mathlib environment, so each check peaks at ~20-27 GiB (see the scorer
``mem_limit`` note in ``apn/task.py``) -- one shared sandbox runs them
sequentially, each a fresh process that releases that footprint on exit, so they
never stack; and a single bring-up means a single container to leak if the run is
interrupted, instead of one per case. The fixture and cases share one
module-scoped event loop (pytest-asyncio ``loop_scope="module"``) -- driving
Inspect's sandbox lifecycle on pytest-asyncio's own loop is the only safe way
(an ``asyncio.run`` in a plain fixture spins up a second loop that its loop-bound
globals deadlock against). Docker is part of the test environment, so this always
runs.
"""

from __future__ import annotations

import io
import re
import tarfile
from contextlib import asynccontextmanager
from pathlib import Path

import pytest
import pytest_asyncio
from inspect_ai.util._sandbox.context import (
    cleanup_sandbox_environments_sample,
    init_sandbox_environments_sample,
)
from inspect_ai.util._sandbox.docker.docker import DockerSandboxEnvironment

import apn.checker as checker_mod
from apn.checker import SandboxSafeVerify
from apn.task import get_compose_file

REPO = Path(__file__).resolve().parent.parent
# Vendored, committed copies of the paper's gold proofs (see the dir's README);
# NOT the gitignored reference_sources/ clone, which is absent in CI.
GOLD_DIR = Path(__file__).resolve().parent / "data" / "gold_proofs"
ISOLATED_DIR = REPO / "apn" / "data" / "oeis" / "Isolated"

# Collected at import time so each conjecture is its own parametrized case.
GOLD_STEMS = sorted(p.stem for p in GOLD_DIR.glob("*.lean"))

# These gold proofs exceed the checker's resource ceilings (scorer mem_limit /
# SafeVerify's 1800s timeout), so a perfect submission would be rejected too;
# skipped until the ceilings are revisited.
RESOURCE_BOUND_STEMS = {
    "A382590_conjecture_kth_prime_factor_is_eventually_periodic",
    "oeis_227582_conjecture_0",
    "oeis_271591_conjecture_0",
}


def _tar_of(files: dict[str, str]) -> bytes:
    """Pack ``{relative path: contents}`` into the tar the checker consumes
    (members relative to ``Submission/``). Mirrors ``test_singlefile_proof.py``."""
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w") as tf:
        for name, content in files.items():
            data = content.encode()
            info = tarfile.TarInfo(name)
            info.size = len(data)
            tf.addfile(info, io.BytesIO(data))
    return buf.getvalue()


@asynccontextmanager
async def _sandbox_envs():
    """Bring up the production compose and yield the live ``{name: env}`` dict.

    Mirrors ``tests/test_singlefile_proof.py::_sandbox_envs``: Inspect's sandbox
    lifecycle against ``apn.task.get_compose_file`` (which builds from
    ``apn/lean/Dockerfile``), so the image is current by construction. The checker
    spans the untrusted ``compile`` and trusted ``scorer`` sandboxes, so we expose
    the whole dict.
    """
    compose = str(get_compose_file(literature=False))
    task_name = "pytest_gold_proofs_scorer"
    await DockerSandboxEnvironment.task_init(task_name, compose)
    try:
        envs = await init_sandbox_environments_sample(
            sandboxenv_type=DockerSandboxEnvironment,
            task_name=task_name,
            config=compose,
            files={},
            setup=None,
            metadata={},
        )
        try:
            yield envs
        finally:
            await cleanup_sandbox_environments_sample(
                type="docker",
                task_name=task_name,
                config=compose,
                environments=envs,
                interrupted=False,
            )
    finally:
        await DockerSandboxEnvironment.task_cleanup(task_name, compose, cleanup=True)


def _target_theorem(spec_text: str) -> str:
    """The single target theorem's name in an isolated spec.

    Every isolated spec in tsoukalas_proved_38 declares exactly one theorem (the conjecture
    target; the cut keeps no surviving dependency lemmas for these), so this is
    unambiguous -- and it is the name ``safe_verify`` will require the submission
    to match."""
    names = re.findall(r"(?m)^theorem\s+([A-Za-z0-9_.]+)", spec_text)
    assert len(names) == 1, f"expected exactly one theorem in spec, found {names}"
    return names[0]


def _gold_submission(stem: str, theorem: str) -> str:
    """The gold proof file for ``stem`` with its target theorem renamed to match
    our spec, ready to pack as ``Submission/Spec.lean``."""
    gold = (GOLD_DIR / f"{stem}.lean").read_text()
    assert gold.count("target_theorem_0") == 1, (
        f"{stem}: expected exactly one 'target_theorem_0' to rename, "
        f"found {gold.count('target_theorem_0')}"
    )
    return gold.replace("target_theorem_0", theorem)


@pytest_asyncio.fixture(loop_scope="module", scope="module")
async def sandbox_envs():
    """The live sandbox-env dict, brought up once and shared by every case.

    Shared (not per-case) is safe here: all gold proofs are honest, and the
    checker clears the compile + score scratch dirs on every call.
    """
    async with _sandbox_envs() as envs:
        yield envs


def test_gold_proofs_present() -> None:
    """The 38 published gold proofs are vendored (guards a silently-empty run)."""
    assert len(GOLD_STEMS) == 38, f"expected 38 gold proofs, found {len(GOLD_STEMS)}: {GOLD_STEMS}"


@pytest.mark.asyncio(loop_scope="module")
@pytest.mark.parametrize(
    "stem",
    [
        pytest.param(
            stem,
            marks=[pytest.mark.skip(reason="exceeds checker resource ceilings")]
            if stem in RESOURCE_BOUND_STEMS
            else [],
        )
        for stem in GOLD_STEMS
    ],
)
async def test_gold_proof_verifies(stem: str, sandbox_envs, monkeypatch) -> None:
    """Each published gold proof is accepted by safe_verify against our spec."""
    monkeypatch.setattr(checker_mod, "sandbox", lambda name=None, *a, **k: sandbox_envs[name])
    target = (ISOLATED_DIR / f"{stem}.lean").read_text()
    submission = _gold_submission(stem, _target_theorem(target))
    outcome = await SandboxSafeVerify(sandbox_name="scorer").check(
        target, _tar_of({"Spec.lean": submission})
    )
    assert outcome.ok, (
        f"gold proof {stem!r} was rejected at stage={outcome.stage!r}:\n"
        f"{outcome.detail[:1500]}"
    )
