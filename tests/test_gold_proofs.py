"""End-to-end regression: the paper's published gold proofs verify CORRECT.

The repo vendors the AlphaProof Nexus paper's solved proofs under
``tests/data/gold_proofs/`` -- one complete, ``sorry``-free Lean proof per
conjecture in the ``tsoukalas_proved_38`` subset (committed copies of the upstream
``reference_sources/.../APNOutputs/OEIS`` files, which are gitignored and absent
in CI; see that dir's README). This test runs each of them through the *real*
:class:`apn.checker.SandboxComparator` against the live ``comparator`` sandbox --
the exact scoring path an eval uses -- and asserts the verdict is accepted. For
each conjecture:

* **spec** = our committed ``apn/data/oeis/Isolated/<stem>.lean`` spec. This is
  the dataset's single source for ``metadata["sketch"]``, i.e. precisely the text
  the checker stages as ``run/Challenge.lean`` at eval time (a leading license
  comment never reaches the export, so reading the file directly is
  verification-equivalent to going through the dataset).
* **submission** = the gold proof file, packed as ``Submission/Spec.lean``, with
  its ``target_theorem_0`` renamed to the spec's own theorem name and the spec's
  appended ``<target>.disproof := sorry`` declaration added (inert under a proof
  claim -- it is not a config target and not in the target's export closure). The
  paper names every challenge theorem ``target_theorem_0``; our specs name it
  after the conjecture, and Comparator matches the configured target by *exact
  name*. A real agent keeps the spec's shape, so this is exactly the submission a
  perfect agent would produce.

This is the complement of every other checker test. Those prove Comparator says
**no** to bad proofs (a ``sorry``/custom axiom/build failure is rejected --
``test_singlefile_proof.py``, ``test_checker.py``) and that our isolated
statements line up with the published ones (the ``test_oeis_isolation.py``
oracle). This proves it says **yes** to the known-good proofs, end to end. It is
the only test that catches the over-strict-checker class: an axiom-allowlist
regression, a Mathlib/toolchain skew, or a ``def``-value mismatch between our
spec and the gold proof -- any of which would silently reject valid proofs and
tank the benchmark with every rejection test still green.

The ``comparator`` sandbox is brought up **once for the whole module** through
Inspect's lifecycle from the production compose (``apn.task.get_compose_file``,
which builds from ``apn/lean/Dockerfile``), exactly like
``tests/test_singlefile_proof.py``, and every conjecture is a parametrized async
case that reuses it -- the checker resets the workspace before each check, so a
shared sandbox is safe for these honest proofs. The fixture and cases share one
module-scoped event loop (pytest-asyncio ``loop_scope="module"``) -- driving
Inspect's sandbox lifecycle on pytest-asyncio's own loop is the only safe way
(an ``asyncio.run`` in a plain fixture spins up a second loop that its loop-bound
globals deadlock against). Docker is part of the test environment, so this always
runs.
"""

from __future__ import annotations

import io
import tarfile
from collections.abc import AsyncIterator
from contextlib import asynccontextmanager
from pathlib import Path

import pytest
import pytest_asyncio
from inspect_ai.util import SandboxEnvironment
from inspect_ai.util._sandbox.context import (
    cleanup_sandbox_environments_sample,
    init_sandbox_environments_sample,
)
from inspect_ai.util._sandbox.docker.docker import DockerSandboxEnvironment

import apn.checker as checker_mod
from apn.checker import SandboxComparator
from apn.dataset import OEIS_DIR, fc_commit, load_manifest
from apn.task import get_compose_file
from scripts.isolation import disproof_declaration, strip_private

REPO = Path(__file__).resolve().parent.parent
# Vendored, committed copies of the paper's gold proofs (see the dir's README);
# NOT the gitignored reference_sources/ clone, which is absent in CI.
GOLD_DIR = Path(__file__).resolve().parent / "data" / "gold_proofs"
ISOLATED_DIR = REPO / "apn" / "data" / "oeis" / "Isolated"

# Collected at import time so each conjecture is its own parametrized case.
GOLD_STEMS = sorted(p.stem for p in GOLD_DIR.glob("*.lean"))

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
async def _sandbox_envs() -> AsyncIterator[dict[str, SandboxEnvironment]]:
    """Bring up the production compose and yield the live ``{name: env}`` dict.

    Mirrors ``tests/test_singlefile_proof.py``: Inspect's sandbox lifecycle
    against ``apn.task.get_compose_file`` (which builds from
    ``apn/lean/Dockerfile``), so the image is current by construction. The
    checker uses the trusted ``comparator`` sandbox, exposed here by name.
    """
    # The gold proofs are OEIS conjectures, so score against the oeis pin's image.
    compose = str(get_compose_file(fc_commit(OEIS_DIR), literature=False))
    task_name = "pytest_gold_proofs_comparator"
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


# The target theorem's fully qualified name for each gold stem, taken from the
# manifest (== the id for all 38, none namespaced). Built once at import.
_DECL_NAME = {r.id: r.decl_name for r in load_manifest(OEIS_DIR)}


def _gold_submission(stem: str, decl: str) -> str:
    """The gold proof file for ``stem`` as ``Submission/Spec.lean``: its
    ``target_theorem_0`` renamed to the spec's target name, its ``private``
    modifiers stripped (the committed specs strip them at isolation, so a real
    agent's submission -- an edit of the spec -- has none; the vendored gold
    files stay verbatim per their README, so the staging transform mirrors the
    strip), and the spec's appended ``<decl>.disproof := sorry`` declaration
    added.

    Under a proof claim Comparator exports only ``<decl>``'s closure, so the
    disproof declaration's ``sorry`` is inert (not a config target, not
    reachable from the proved theorem); it is present only so the submission is
    shape-compatible with the committed spec a real agent edits."""
    gold = (GOLD_DIR / f"{stem}.lean").read_text()
    assert gold.count("target_theorem_0") == 1, (
        f"{stem}: expected exactly one 'target_theorem_0' to rename, "
        f"found {gold.count('target_theorem_0')}"
    )
    renamed = strip_private(gold.replace("target_theorem_0", decl))
    return renamed.rstrip() + "\n\n" + disproof_declaration(decl) + "\n"


@pytest_asyncio.fixture(loop_scope="module", scope="module")
async def sandbox_envs() -> AsyncIterator[dict[str, SandboxEnvironment]]:
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
@pytest.mark.parametrize("stem", GOLD_STEMS)
async def test_gold_proof_verifies(
    stem: str,
    sandbox_envs: dict[str, SandboxEnvironment],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Each published gold proof is accepted by Comparator against our spec."""
    monkeypatch.setattr(checker_mod, "sandbox", lambda name=None, *a, **k: sandbox_envs["comparator"])
    spec = (ISOLATED_DIR / f"{stem}.lean").read_text()
    decl = _DECL_NAME[stem]
    submission = _gold_submission(stem, decl)
    outcome = await SandboxComparator().check(
        spec, _tar_of({"Spec.lean": submission}), decl=decl, claim="proof"
    )
    assert outcome.ok, (
        f"gold proof {stem!r} was rejected at stage={outcome.stage!r}:\n"
        f"{outcome.detail[-2000:]}"
    )
