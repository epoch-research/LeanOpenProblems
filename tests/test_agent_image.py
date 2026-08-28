"""Contract test for the agent image's declared compute stack.

The agent image's tool roster is *declared* -- in ``apn/lean/compute-env.yaml``
plus the explicit install lines of the Dockerfile's ``compute_build``/
``solvers_build``/``agent`` stages -- and advertised to the agent by
``apn.prompts.user_prompt``. This suite is the hardcoded contract between the
two: every advertised binary resolves, every advertised python module imports,
a handful of end-to-end smokes prove the big tools actually run (a present
binary with a broken runtime, e.g. a Sage missing its GAP, would pass a bare
``command -v``), and the vendored docs directories exist. If an install line is
dropped or a conda pin stops shipping a binary, this fails before an eval does.

Every exec runs through ``bash --login -c`` -- exactly how the agent's bash
tool executes (``apn.tools``) -- so the PATH plumbing (/opt/env/bin first, via
/etc/profile.d) is itself under test.

The agent (``default``) sandbox is brought up **once for the whole module**
through Inspect's lifecycle from the production compose
(``apn.task.get_compose_file``, which builds from ``apn/lean/Dockerfile``),
exactly like ``tests/test_gold_proofs.py``, sharing one module-scoped event
loop. Docker is part of the test environment, so this always runs.
"""

from __future__ import annotations

from collections.abc import AsyncIterator
from contextlib import asynccontextmanager

import pytest
import pytest_asyncio
from inspect_ai.util import SandboxEnvironment
from inspect_ai.util._sandbox.context import (
    cleanup_sandbox_environments_sample,
    init_sandbox_environments_sample,
)
from inspect_ai.util._sandbox.docker.docker import DockerSandboxEnvironment

from apn.dataset import OEIS_DIR, fc_commit
from apn.task import get_compose_file

# --------------------------------------------------------------------------- #
# The contract: hardcoded rosters (no manifest machinery by design -- these    #
# lists and the Dockerfile install lines are maintained together by hand).     #
# --------------------------------------------------------------------------- #

# Binaries, by provenance:
BINARIES = [
    # lean layer (base) + loogle_build
    "lake",
    "lean",
    "loogle",
    # conda env (/opt/env/bin; spec: compute-env.yaml)
    "python3",
    "sage",
    "gp",
    "gap",
    "Singular",
    "maxima",
    "z3",
    "primesieve",
    "primecount",
    "ecm",
    "geng",
    "genbg",
    "normaliz",
    "zsolve",
    "lrs",
    # solvers_build (/usr/local/bin)
    "kissat",
    "plantri",
    "cvc5",
    "msolve",
    "prover9",
    "mace4",
    # apt (bookworm)
    "polymake",
    "M2",
    "regina-python",
    "cryptominisat",
    "csdp",
    "jq",
    "rg",
    "git",
]

# Python modules importable from the agent's `python3` (the /opt/env python).
PYTHON_MODULES = [
    "numpy",
    "scipy",
    "sympy",
    "mpmath",
    "pandas",
    "networkx",
    "igraph",
    "flint",  # python-flint
    "highspy",
    "fpylll",
    "z3",
    "cvc5",
    "ortools",
    "pysat",  # python-sat
    "snappy",  # SnapPy
    # ore_algebra is a sage library: importing it before sage.all trips sage's
    # circular-import guard, so the contract (and the agent's usage) is
    # "import sage.all first".
    "sage.all, ore_algebra",
    "sage.all",
]

# Vendored docs directories (apn/lean/docs/<tool> -> /opt/docs/<tool>).
DOCS_DIRS = [
    "loogle",
    "nauty",
    "plantri",
    "polymake",
    "normaliz",
    "4ti2",
    "lrslib",
    "msolve",
    "csdp",
    "prover9",
    "regina",
    "snappy",
    "ore_algebra",
    "python-flint",
]


@asynccontextmanager
async def _sandbox_envs() -> AsyncIterator[dict[str, SandboxEnvironment]]:
    """Bring up the production compose and yield the live ``{name: env}`` dict
    (mirrors ``tests/test_gold_proofs.py``; the agent workspace is ``default``)."""
    compose = str(get_compose_file(fc_commit(OEIS_DIR), literature=False))
    task_name = "pytest_agent_image"
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


@pytest_asyncio.fixture(loop_scope="module", scope="module")
async def agent_env() -> AsyncIterator[SandboxEnvironment]:
    async with _sandbox_envs() as envs:
        yield envs["default"]


async def _bash(
    env: SandboxEnvironment, command: str, timeout: int = 120
) -> tuple[int, str, str]:
    """Run ``command`` exactly as the agent's bash tool does (login shell)."""
    result = await env.exec(["bash", "--login", "-c", command], timeout=timeout)
    return result.returncode, result.stdout, result.stderr


@pytest.mark.asyncio(loop_scope="module")
@pytest.mark.parametrize("binary", BINARIES)
async def test_binary_on_path(agent_env: SandboxEnvironment, binary: str) -> None:
    code, stdout, stderr = await _bash(agent_env, f"command -v {binary}")
    assert code == 0, f"binary {binary!r} not on the agent's login-shell PATH"


@pytest.mark.asyncio(loop_scope="module")
@pytest.mark.parametrize("module", PYTHON_MODULES)
async def test_python_module_imports(
    agent_env: SandboxEnvironment, module: str
) -> None:
    # Sage-adjacent imports (sage.all, ore_algebra, snappy) are slow cold.
    code, stdout, stderr = await _bash(
        agent_env, f"python3 -c 'import {module}'", timeout=300
    )
    assert code == 0, f"import {module} failed:\n{stderr[-2000:]}"


@pytest.mark.asyncio(loop_scope="module")
@pytest.mark.parametrize("tool", DOCS_DIRS)
async def test_docs_dir_present(agent_env: SandboxEnvironment, tool: str) -> None:
    # Non-empty, not merely present.
    code, stdout, _ = await _bash(agent_env, f"ls /opt/docs/{tool} | head -1")
    assert code == 0 and stdout.strip(), f"/opt/docs/{tool} missing or empty"


# --------------------------------------------------------------------------- #
# End-to-end smokes: the big tools actually run.                               #
# --------------------------------------------------------------------------- #


@pytest.mark.asyncio(loop_scope="module")
async def test_sage_factors(agent_env: SandboxEnvironment) -> None:
    code, stdout, stderr = await _bash(
        agent_env, "sage -c 'print(factor(2^67-1))'", timeout=600
    )
    assert code == 0, f"sage failed:\n{stderr[-2000:]}"
    assert stdout.strip() == "193707721 * 761838257287"


@pytest.mark.asyncio(loop_scope="module")
async def test_geng_counts_graphs_on_five_vertices(
    agent_env: SandboxEnvironment,
) -> None:
    code, stdout, _ = await _bash(agent_env, "geng -q 5 | wc -l")
    assert code == 0
    assert stdout.strip() == "34"


@pytest.mark.asyncio(loop_scope="module")
async def test_cpsat_solves_trivial_model(agent_env: SandboxEnvironment) -> None:
    script = (
        "from ortools.sat.python import cp_model\n"
        "m = cp_model.CpModel()\n"
        "x = m.new_int_var(0, 10, 'x')\n"
        "m.add(x > 7)\n"
        "s = cp_model.CpSolver()\n"
        "assert s.solve(m) == cp_model.OPTIMAL\n"
        "print(s.value(x))\n"
    )
    code, stdout, stderr = await _bash(
        agent_env, f"python3 - <<'EOF'\n{script}EOF", timeout=300
    )
    assert code == 0, f"CP-SAT smoke failed:\n{stderr[-2000:]}"


@pytest.mark.asyncio(loop_scope="module")
async def test_loogle_finds_nat_prime(agent_env: SandboxEnvironment) -> None:
    # Cold start loads the prebuilt index + Mathlib oleans; generous timeout.
    code, stdout, stderr = await _bash(
        agent_env, "loogle 'Nat.Prime'", timeout=900
    )
    assert code == 0, f"loogle failed:\n{stderr[-2000:]}"
    assert "Nat.Prime" in stdout


@pytest.mark.asyncio(loop_scope="module")
async def test_trace_state_prints_goal(agent_env: SandboxEnvironment) -> None:
    """The prompt's advertised goal-state idiom: `trace_state` before a `sorry`
    prints the goal on stdout under `lake env lean` (regression-pins the
    workflow the agent is told to use, in the real Lake project)."""
    lean = (
        "import Mathlib.Tactic\\n"
        "example (a b : Nat) : a + b = b + a := by\\n"
        "  trace_state\\n"
        "  sorry\\n"
    )
    code, stdout, stderr = await _bash(
        agent_env,
        "cd /workspace/leanproject && mkdir -p Submission "
        f"&& printf '{lean}' > Submission/TraceStateSmoke.lean "
        "&& lake env lean Submission/TraceStateSmoke.lean; rc=$?; "
        "rm -f Submission/TraceStateSmoke.lean; exit $rc",
        timeout=600,
    )
    # `sorry` warns but exits 0; the goal state must appear on stdout.
    assert code == 0, f"lake env lean failed:\n{stderr[-2000:]}\n{stdout[-2000:]}"
    assert "a + b = b + a" in stdout, f"goal state not printed:\n{stdout[-2000:]}"
