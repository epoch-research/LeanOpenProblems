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

import platform
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
    "clingo",
    "primesieve",
    "primecount",
    "ecm",
    "geng",
    "genbg",
    "gentreeg",
    "gentourng",
    "vcolg",
    "shortg",
    "labelg",
    "showg",
    "amtog",
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
    "vampire",
    "drat-trim",
    "lrat-check",
    "cake_lpr",
    "breakid",
    "smsg",
    "march_cu",
    "msieve",
    "redumis",
    "gclc",
    # julia_build
    "julia",
    # apt (bookworm)
    "polymake",
    "M2",
    "regina-python",
    "cryptominisat",
    "csdp",
    "topcom-points2triangs",
    "cadabra2",
    "minizinc",
    "berkeley-abc",
    "eprover",
    "mpsolve",
    "java",
    "jq",
    "rg",
    "git",
    "gcc",
    "make",
]

# The special-form primality toolchain: absent from arm64 images (local dev
# on Apple silicon); CI and production images are amd64. sllr64/pfgw64 are
# x86-64 gwnum assembly; srsieve2's makefile only knows x86 and 32-bit ARM.
BINARIES_X86_ONLY = [
    "sllr64",
    "pfgw64",
    "srsieve2",
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
    "cvxpy",
    "pyscipopt",
    "clingo",
    "graphillion",
    "libsemigroups_pybind11",
    "pymanopt",
    "pysindy",
    "hypothesis",
    "sage.all",
]

# Docs directories, downloaded at image build from pinned upstream sources
# (Dockerfile `docs_fetch` stage -> /opt/docs/<tool>).
DOCS_DIRS = [
    "loogle",
    "plantri",
    "normaliz",
    "4ti2",
    "lrslib",
    "msolve",
    "csdp",
    "regina",
    "snappy",
    "python-flint",
    "sms",
    "graphillion",
    "breakid",
    "drat-trim",
    "cake_lpr",
    "kamis",
    "gclc",
    "msieve",
    "walnut",
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
@pytest.mark.parametrize("binary", BINARIES_X86_ONLY)
@pytest.mark.skipif(
    platform.machine() in ("arm64", "aarch64"),
    reason="x86-64-only binaries; the sandbox is built for the host arch",
)
async def test_x86_binary_on_path(agent_env: SandboxEnvironment, binary: str) -> None:
    code, stdout, stderr = await _bash(agent_env, f"command -v {binary}")
    assert code == 0, f"binary {binary!r} not on the agent's login-shell PATH"


@pytest.mark.asyncio(loop_scope="module")
async def test_walnut_launcher_present(agent_env: SandboxEnvironment) -> None:
    # Walnut is a tree at /opt/walnut, not a PATH binary; the prompt advertises
    # its upstream launcher path verbatim.
    code, stdout, _ = await _bash(agent_env, "test -x /opt/walnut/walnut.sh")
    assert code == 0, "/opt/walnut/walnut.sh missing or not executable"


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
async def test_kissat_drattrim_roundtrip(agent_env: SandboxEnvironment) -> None:
    """An UNSAT claim is only usable if its certificate checks: kissat emits a
    DRAT proof (exit 20 = UNSAT), drat-trim verifies it (s VERIFIED)."""
    code, stdout, stderr = await _bash(
        agent_env,
        "cd /tmp && printf 'p cnf 1 2\\n1 0\\n-1 0\\n' > smoke.cnf "
        "&& kissat -q smoke.cnf smoke.drat; test $? -eq 20 "
        "&& drat-trim smoke.cnf smoke.drat; rc=$?; rm -f smoke.cnf smoke.drat; exit $rc",
    )
    assert code == 0, f"kissat/drat-trim roundtrip failed:\n{stdout[-1000:]}{stderr[-1000:]}"


@pytest.mark.asyncio(loop_scope="module")
async def test_gap_small_group(agent_env: SandboxEnvironment) -> None:
    # The conda GAP ships the SmallGrp library; its absence would silently
    # gut the group-theory workflow the prompt implies.
    code, stdout, stderr = await _bash(
        agent_env, "gap -q -c 'Print(Size(SmallGroup(64, 1)), \"\\n\"); QUIT;'", timeout=300
    )
    assert code == 0, f"gap failed:\n{stderr[-2000:]}"
    # gap prints informational "#I ..." banner lines before the answer.
    assert stdout.strip().splitlines()[-1] == "64", stdout[-2000:]


@pytest.mark.asyncio(loop_scope="module")
async def test_scip_solves_miqcp(agent_env: SandboxEnvironment) -> None:
    # pyscipopt's wheel bundles libscip; max x+y s.t. x^2+y^2<=25, x integer.
    script = (
        "from pyscipopt import Model\n"
        "m = Model()\n"
        "x = m.addVar('x', vtype='I', lb=0, ub=10)\n"
        "y = m.addVar('y', lb=0, ub=5)\n"
        "m.addCons(x*x + y*y <= 25)\n"
        "m.setObjective(x + y, 'maximize')\n"
        "m.hideOutput()\n"
        "m.optimize()\n"
        "assert m.getStatus() == 'optimal', m.getStatus()\n"
        "assert abs(m.getObjVal() - 7) < 1e-4, m.getObjVal()\n"
    )
    code, stdout, stderr = await _bash(
        agent_env, f"python3 - <<'EOF'\n{script}EOF", timeout=300
    )
    assert code == 0, f"SCIP smoke failed:\n{stderr[-2000:]}"


@pytest.mark.asyncio(loop_scope="module")
async def test_vampire_refutes(agent_env: SandboxEnvironment) -> None:
    code, stdout, stderr = await _bash(
        agent_env,
        "printf 'fof(a, axiom, p).\\nfof(c, conjecture, p).\\n' "
        "| vampire --time_limit 30",
    )
    assert code == 0, f"vampire failed:\n{stderr[-2000:]}\n{stdout[-2000:]}"
    assert "Refutation" in stdout


@pytest.mark.asyncio(loop_scope="module")
async def test_walnut_decides_trivial_property(agent_env: SandboxEnvironment) -> None:
    # Walnut ships the Thue-Morse word T; a universally true statement about
    # it must come back TRUE (proves the jar + word automata actually load).
    code, stdout, stderr = await _bash(
        agent_env,
        "cd /opt/walnut && printf 'eval smoketest \"?msd_2 An T[n]=T[n]\";\\nexit;\\n' | ./walnut.sh",
        timeout=300,
    )
    assert code == 0, f"walnut failed:\n{stderr[-2000:]}\n{stdout[-2000:]}"
    assert "TRUE" in stdout, f"expected TRUE:\n{stdout[-2000:]}"


@pytest.mark.asyncio(loop_scope="module")
async def test_julia_oscar_loads(agent_env: SandboxEnvironment) -> None:
    # The baked depot must load offline with no re-precompilation surprises.
    code, stdout, stderr = await _bash(
        agent_env,
        "julia -e 'using Oscar; println(order(symmetric_group(4)))'",
        timeout=600,
    )
    assert code == 0, f"julia/Oscar failed:\n{stderr[-2000:]}"
    assert stdout.strip().endswith("24")


@pytest.mark.asyncio(loop_scope="module")
async def test_loogle_finds_nat_prime(agent_env: SandboxEnvironment) -> None:
    # Upstream's documented invocation (vendored at /opt/docs/loogle): from
    # the project, via `lake env`. The Mathlib index is prebuilt in the image,
    # so this must not fall into the slow index-construction path -- but cold
    # start still imports Mathlib, hence the generous timeout.
    code, stdout, stderr = await _bash(
        agent_env,
        "cd /workspace/leanproject && lake env loogle --module Mathlib 'Nat.Prime'",
        timeout=900,
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
