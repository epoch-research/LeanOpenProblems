"""Contract test for the agent image's declared compute stack.

The agent image's tool roster is *declared* -- in ``apn/lean/sage.yaml`` and
``apn/lean/conda.yaml`` (the two conda-forge envs), the per-tool scripts under
``apn/lean`` (``unpackaged/*.sh``, ``sage/*.sh``, ``walnut.sh``, ``julia.sh``),
the ``agent`` stage's apt line, and the exposure list ``apn/lean/agent-commands``
-- and advertised to the agent by ``apn.prompts.user_prompt``. This suite is
the hardcoded contract between the two: every advertised binary resolves, every
advertised python module imports in the interpreter that owns it (the agent's
``python3``, or Sage's own via ``sage -c``), a handful of end-to-end smokes prove
the big tools actually run (a present binary with a broken runtime, e.g. a Sage
missing its GAP, would pass a bare ``command -v``), the shipped docs directories
exist, and the assembly invariants the Dockerfile leaves to tests hold: every
``agent-commands`` entry is what its name resolves to, the cvc5 binary and
wheel agree, the two pythons are distinct. If an install line is dropped or a
conda pin stops shipping a binary, this fails before an eval does.

Every exec runs through ``bash --login -c`` -- exactly how the agent's bash
tool executes (``apn.tools``) -- so the exposure mechanism (symlinks in
/usr/local/bin, plus the ``sage`` wrapper, which a login shell's PATH puts
ahead of /usr/bin) is itself under test.

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
from pathlib import Path

import pytest
import pytest_asyncio
from inspect_ai.util import SandboxEnvironment
from inspect_ai.util._sandbox.context import (
    cleanup_sandbox_environments_sample,
    init_sandbox_environments_sample,
)
from inspect_ai.util._sandbox.docker.docker import DockerSandboxEnvironment

import apn
from apn.dataset import OEIS_DIR, fc_commit
from apn.layout import SUBMISSION_DIR
from apn.task import get_compose_file

# --------------------------------------------------------------------------- #
# The contract: hardcoded rosters (no manifest machinery by design -- these    #
# lists and the image's declarations are maintained together by hand).        #
# --------------------------------------------------------------------------- #

# Binaries, by provenance:
BINARIES = [
    # lean layer (base) + loogle
    "lake",
    "lean",
    "loogle",
    # the sage env (/opt/sage; spec: sage.yaml), via agent-commands
    "sage",
    "gp",
    "gap",
    "Singular",
    "maxima",
    # the conda env (/opt/env; spec: conda.yaml), via agent-commands
    "python3",
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
    # unpackaged (/usr/local/bin; recipes: unpackaged/<tool>.sh)
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
    # julia (julia.sh), via agent-commands
    "julia",
    # apt (bookworm)
    "polymake",
    "M2",
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
    "autograd",  # pymanopt's autodiff backend
    "pysindy",
    "hypothesis",
]

# Regina's wheels are x86-64 only (conda.yaml's environment marker), like the
# primality binaries above.
PYTHON_MODULES_X86_ONLY = [
    "regina",
]

# Python modules importable from Sage's own python (the /opt/sage env, reached
# through the `sage` launcher: `sage -c`, `sage <file.py>`): sage itself and its
# optional backends/databases (sage.yaml plus the sage/*.sh scripts).
# Deliberately NOT in the agent's `python3`.
SAGE_PYTHON_MODULES = [
    "sage.all",
    "PyNormaliz",
    "pycryptosat",
    "pycosat",
    "symengine",
    "sagemath_giac",
    "database_knotinfo",
    "matroid_database",
    "database_cubic_hecke",
]

# Docs shipped alongside the unpackaged tools (each recipe installs them from
# the archive it builds) and Loogle's README, at /usr/local/share/doc/<tool>.
DOCS_DIRS = [
    "kissat",
    "plantri",
    "prover9",
    "msolve",
    "drat-trim",
    "cake_lpr",
    "breakid",
    "sms",
    "march_cu",
    "msieve",
    "kamis",
    "gclc",
    "loogle",
]

# The exposure list the agent stage symlinks into /usr/local/bin, one absolute
# path per line (see the Dockerfile's agent stage).
AGENT_COMMANDS = [
    line
    for line in (Path(apn.__file__).parent / "lean" / "agent-commands")
    .read_text()
    .splitlines()
    if line
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
    # Present is not runnable: a binary whose shared libraries do not resolve
    # passes `command -v` and dies on start (breakid shipped that way once --
    # its executable wanted a libbreakid.so that never left the build stage).
    # This is also what holds the unpackaged recipes to their contract of
    # linking only what the bookworm userland provides. `ldd` on a script or a
    # static binary exits non-zero and reports nothing "not found", so this is
    # a no-op for those. readlink -f: the env launchers, java and julia are
    # reached via symlinks and locate their libraries by an $ORIGIN rpath,
    # which ldd resolves from the path it is given, not the real file.
    code, stdout, stderr = await _bash(
        agent_env,
        f'ldd "$(readlink -f "$(command -v {binary})")" 2>/dev/null | grep "not found" || true',
    )
    assert stdout.strip() == "", f"binary {binary!r} has unresolved shared libraries:\n{stdout}"


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
@pytest.mark.parametrize(
    "path", AGENT_COMMANDS, ids=[p.rsplit("/", 1)[1] for p in AGENT_COMMANDS]
)
async def test_agent_command_resolves(agent_env: SandboxEnvironment, path: str) -> None:
    """Every agent-commands entry exists, is executable, and is what its bare
    name resolves to in a login shell. The agent stage's `ln -s` makes a
    dangling link out of a typo without complaint; this is where that shows."""
    name = path.rsplit("/", 1)[1]
    code, stdout, stderr = await _bash(
        agent_env,
        f'test -x "{path}" && readlink -f "{path}" && readlink -f "$(command -v {name})"',
    )
    assert code == 0, f"{path} missing or not executable:\n{stderr[-2000:]}"
    listed, resolved = stdout.split()
    assert resolved == listed, f"{name} resolves to {resolved}, not the listed {path}"


@pytest.mark.asyncio(loop_scope="module")
async def test_sage_wrapper_is_the_launcher(agent_env: SandboxEnvironment) -> None:
    """`sage` is the one exposed command that is a wrapper, not a link: Sage
    starts helpers by bare name and needs its env's bin on its own PATH
    (apn/lean/sage/sage)."""
    code, stdout, stderr = await _bash(
        agent_env, 'test -x /usr/local/bin/sage && readlink -f "$(command -v sage)"'
    )
    assert code == 0, f"sage wrapper missing:\n{stderr[-2000:]}"
    assert stdout.strip() == "/usr/local/bin/sage", stdout


@pytest.mark.asyncio(loop_scope="module")
async def test_sage_subprocess_interfaces(agent_env: SandboxEnvironment) -> None:
    """Sage interfaces that start a separate program (giac, lcalc) find it.
    This is the route an in-process `import sage.libs.giac` does not cover:
    with Sage's bin off its PATH, giac() failed to start and lcalc calls
    returned [] with exit 0."""
    code, stdout, stderr = await _bash(
        agent_env, "sage -c 'print(giac(\"1+1\"))'", timeout=600
    )
    assert code == 0, f"giac() failed:\n{stderr[-2000:]}\n{stdout[-2000:]}"
    assert stdout.strip().splitlines()[-1] == "2", stdout[-2000:]
    code, stdout, stderr = await _bash(
        agent_env,
        "sage -c 'from sage.lfunctions.lcalc import lcalc; print(lcalc.zeros(2))'",
        timeout=600,
    )
    assert code == 0, f"lcalc failed:\n{stderr[-2000:]}\n{stdout[-2000:]}"
    assert "14.1347251" in stdout, stdout[-2000:]


@pytest.mark.asyncio(loop_scope="module")
async def test_sage_cython_compiles(agent_env: SandboxEnvironment) -> None:
    # Compiling Cython needs pkg-config on Sage's PATH and setuptools
    # (distutils) in Sage's env (sage.yaml). The file-based cython_import is
    # used because the string form, cython("..."), compiles into the REPL's
    # user globals, which `sage -c` never initializes.
    code, stdout, stderr = await _bash(
        agent_env,
        "printf 'cpdef int seven():\\n    return 7\\n' > /tmp/seven.pyx && "
        "sage -c 'from sage.misc.cython import cython_import; "
        "print(cython_import(\"/tmp/seven.pyx\").seven())'",
        timeout=900,
    )
    assert code == 0, f"cython_import failed:\n{stderr[-2000:]}\n{stdout[-2000:]}"
    assert stdout.strip().splitlines()[-1] == "7", stdout[-2000:]


@pytest.mark.asyncio(loop_scope="module")
async def test_env_man_pages_on_manpath(agent_env: SandboxEnvironment) -> None:
    # The envs' bin dirs are not on PATH, so their man pages need the explicit
    # manpath entries the agent stage adds.
    code, stdout, stderr = await _bash(agent_env, "man -w primesieve && man -w Singular")
    assert code == 0, f"man pages not found:\n{stderr[-2000:]}"


@pytest.mark.asyncio(loop_scope="module")
async def test_walnut_launcher_present(agent_env: SandboxEnvironment) -> None:
    # Walnut is a tree at /opt/walnut, not a PATH binary; the prompt names the
    # location and Walnut's own README documents running ./walnut.sh from it.
    code, stdout, _ = await _bash(agent_env, "test -x /opt/walnut/walnut.sh")
    assert code == 0, "/opt/walnut/walnut.sh missing or not executable"


@pytest.mark.asyncio(loop_scope="module")
@pytest.mark.parametrize("module", PYTHON_MODULES)
async def test_python_module_imports(
    agent_env: SandboxEnvironment, module: str
) -> None:
    # snappy and the solver bindings are slow cold.
    code, stdout, stderr = await _bash(
        agent_env, f"python3 -c 'import {module}'", timeout=300
    )
    assert code == 0, f"import {module} failed:\n{stderr[-2000:]}"


@pytest.mark.asyncio(loop_scope="module")
@pytest.mark.parametrize("module", PYTHON_MODULES_X86_ONLY)
@pytest.mark.skipif(
    platform.machine() in ("arm64", "aarch64"),
    reason="x86-64-only wheels; the sandbox is built for the host arch",
)
async def test_x86_python_module_imports(
    agent_env: SandboxEnvironment, module: str
) -> None:
    code, stdout, stderr = await _bash(
        agent_env, f"python3 -c 'import {module}'", timeout=300
    )
    assert code == 0, f"import {module} failed:\n{stderr[-2000:]}"


@pytest.mark.asyncio(loop_scope="module")
@pytest.mark.parametrize("module", SAGE_PYTHON_MODULES)
async def test_sage_python_module_imports(
    agent_env: SandboxEnvironment, module: str
) -> None:
    # `sage -c` runs in Sage's interpreter (after loading sage.all; slow cold).
    code, stdout, stderr = await _bash(
        agent_env, f"sage -c 'import {module}'", timeout=600
    )
    assert code == 0, f"sage -c: import {module} failed:\n{stderr[-2000:]}"


@pytest.mark.asyncio(loop_scope="module")
async def test_two_pythons_are_distinct(agent_env: SandboxEnvironment) -> None:
    """The agent's `python3` is the conda env's; Sage's is reached only through
    the `sage` launcher; `pip` belongs to the agent's; and Sage is invisible to
    the agent's python3 (the split is what frees the python stack's pins from
    Sage's)."""
    code, stdout, stderr = await _bash(
        agent_env,
        "python3 -c 'import sys; print(sys.prefix)'"
        " && sage -c 'import sys; print(sys.prefix)'"
        ' && readlink -f "$(command -v pip)"',
        timeout=300,
    )
    assert code == 0, f"interpreter probe failed:\n{stderr[-2000:]}"
    agent_prefix, sage_prefix, pip = stdout.split()
    assert agent_prefix == "/opt/env", stdout
    assert sage_prefix == "/opt/sage", stdout
    assert pip.startswith("/opt/env/"), stdout
    code, _, _ = await _bash(agent_env, "python3 -c 'import sage'")
    assert code != 0, "the agent's python3 must not see Sage"


@pytest.mark.asyncio(loop_scope="module")
async def test_cvc5_binary_matches_bindings(agent_env: SandboxEnvironment) -> None:
    """The one cross-chunk version agreement: the cvc5 binary
    (unpackaged/cvc5.sh) and the cvc5 wheel (conda.yaml) are pinned
    separately and must be the same release."""
    code, stdout, stderr = await _bash(
        agent_env,
        "cvc5 --version | head -1 | awk '{print $2}'"
        " && python3 -c 'import cvc5; print(cvc5.__version__)'",
        timeout=300,
    )
    assert code == 0, f"cvc5 version probe failed:\n{stderr[-2000:]}"
    binary, wheel = stdout.split()
    assert binary == wheel, f"cvc5 binary {binary} vs python bindings {wheel}"


@pytest.mark.asyncio(loop_scope="module")
@pytest.mark.parametrize("tool", DOCS_DIRS)
async def test_docs_dir_present(agent_env: SandboxEnvironment, tool: str) -> None:
    # Non-empty, not merely present.
    code, stdout, _ = await _bash(agent_env, f"ls /usr/local/share/doc/{tool} | head -1")
    assert code == 0 and stdout.strip(), f"/usr/local/share/doc/{tool} missing or empty"


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
async def test_gp_arithmetic(agent_env: SandboxEnvironment) -> None:
    code, stdout, stderr = await _bash(agent_env, "echo 'print(1+1); quit' | gp -q")
    assert code == 0, f"gp failed:\n{stderr[-2000:]}"
    assert stdout.strip() == "2"


@pytest.mark.asyncio(loop_scope="module")
async def test_singular_arithmetic(agent_env: SandboxEnvironment) -> None:
    code, stdout, stderr = await _bash(agent_env, "Singular -q -c 'print(2+2); quit;'")
    assert code == 0, f"Singular failed:\n{stderr[-2000:]}"
    assert stdout.strip() == "4"


@pytest.mark.asyncio(loop_scope="module")
async def test_maxima_integrates(agent_env: SandboxEnvironment) -> None:
    code, stdout, stderr = await _bash(
        agent_env,
        "maxima --very-quiet --batch-string='display2d:false$ print(integrate(x^2,x))$'",
        timeout=300,
    )
    assert code == 0, f"maxima failed:\n{stderr[-2000:]}"
    assert "x^3/3" in stdout, stdout[-2000:]


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


# Sage optional features the image declares (sage.features names). Sage's own
# detection is the contract: each must report present in the agent's sage.
SAGE_OPTIONAL_FEATURES = [
    "pynormaliz",
    "sage.libs.giac",
    "pycryptosat",
    "pycosat",
    "symengine_py",
    "gap_package_grape",
    "gap_package_guava",
    "gap_package_hap",
    "gap_package_design",
    "gap_package_qpa",
    "gap_package_quagroup",
    "database_cremona_ellcurve",
    "database_jones_numfield",
    "database_knotinfo",
    "matroid_database",
    "database_cubic_hecke",
]


@pytest.mark.asyncio(loop_scope="module")
async def test_sage_optional_features_present(agent_env: SandboxEnvironment) -> None:
    """Every declared Sage optional backend/database is detected by Sage itself."""
    names = ",".join(SAGE_OPTIONAL_FEATURES)
    code, stdout, stderr = await _bash(
        agent_env,
        "sage -c '"
        "from sage.features.all import all_features\n"
        f"want = set(\"{names}\".split(\",\"))\n"
        "feats = {f.name: f for f in all_features()}\n"
        "unknown = sorted(want - set(feats))\n"
        "missing = sorted(n for n in want & set(feats) if not feats[n].is_present())\n"
        "print(\"unknown:\", unknown); print(\"missing:\", missing)'",
        timeout=600,
    )
    assert code == 0, f"sage features check failed:\n{stderr[-2000:]}\n{stdout[-2000:]}"
    assert "unknown: []" in stdout, stdout
    assert "missing: []" in stdout, stdout


@pytest.mark.asyncio(loop_scope="module")
async def test_sage_optional_backends_compute(agent_env: SandboxEnvironment) -> None:
    """The backends do real work through Sage: Normaliz (Ehrhart polynomial),
    Giac (Groebner basis), CryptoMiniSat (a SAT instance), GRAPE via libgap,
    and the Cremona and Odlyzko databases."""
    code, stdout, stderr = await _bash(
        agent_env,
        "sage -c '"
        "P = Polyhedron(vertices=[[0,0],[1,0],[0,1],[1,1]], backend=\"normaliz\")\n"
        "assert str(P.ehrhart_polynomial(engine=\"normaliz\")) == \"t^2 + 2*t + 1\"\n"
        "R = PolynomialRing(QQ, \"x,y\"); x, y = R.gens()\n"
        "assert R.ideal([x^2 - y, y^2 - x]).groebner_basis(algorithm=\"giac\") == [x^2 - y, y^2 - x]\n"
        "from sage.sat.solvers import CryptoMiniSat\n"
        "s = CryptoMiniSat(); s.add_clause((1, 2)); s.add_clause((-1,)); assert s()[2] is True\n"
        "libgap.eval(\"LoadPackage(\\\"grape\\\")\")\n"
        "assert str(libgap.eval(\"GlobalParameters(JohnsonGraph(5,2))\")) == \"[ [ 0, 0, 6 ], [ 1, 3, 2 ], [ 4, 2, 0 ] ]\"\n"
        "assert CremonaDatabase().largest_conductor() == 499998\n"
        "assert abs(float(zeta_zeros()[0]) - 14.134725142) < 1e-8\n"
        "print(\"ok\")'",
        timeout=900,
    )
    assert code == 0, f"sage backends smoke failed:\n{stderr[-2000:]}\n{stdout[-2000:]}"
    assert "ok" in stdout


@pytest.mark.asyncio(loop_scope="module")
async def test_ortools_and_cvxpy_coexist(agent_env: SandboxEnvironment) -> None:
    """CP-SAT plus a cvxpy solve through OR-Tools' GLOP, in one interpreter.

    Regression-pins the libhighs clash: with conda highspy installed, whichever
    of highspy/ortools imported second failed on an undefined symbol, and
    cvxpy's GLOP/PDLP backends (which load ortools) failed the same way. The
    spec pins cvxpy-base and no highspy so nothing else preloads a libhighs."""
    code, stdout, stderr = await _bash(
        agent_env,
        "python3 -c '"
        "from ortools.sat.python import cp_model\n"
        "import cvxpy as cp\n"
        "m = cp_model.CpModel(); v = m.NewIntVar(0, 5, \"v\"); m.Add(v >= 3)\n"
        "s = cp_model.CpSolver(); assert s.StatusName(s.Solve(m)) == \"OPTIMAL\"\n"
        "x = cp.Variable(); p = cp.Problem(cp.Minimize(x), [x >= 1])\n"
        "for solver in (\"GLOP\", \"PDLP\", \"CLARABEL\"):\n"
        "    p.solve(solver=solver); assert abs(x.value - 1) < 1e-6, solver\n"
        "print(\"ok\")'",
        timeout=600,
    )
    assert code == 0, f"ortools+cvxpy failed:\n{stderr[-2000:]}\n{stdout[-2000:]}"
    assert "ok" in stdout


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
async def test_gap_digraphs_loads(agent_env: SandboxEnvironment) -> None:
    # Digraphs and its kernel dependencies (io, orb, datastructures) come from
    # the GAP packages tarball (sage/gap-packages.sh); the conda GAP ships none.
    code, stdout, stderr = await _bash(
        agent_env,
        "gap -q -c 'LoadPackage(\"digraphs\"); "
        "Print(DigraphNrEdges(CompleteDigraph(5)), \"\\n\"); QUIT;'",
        timeout=300,
    )
    assert code == 0, f"gap failed:\n{stderr[-2000:]}\n{stdout[-2000:]}"
    assert stdout.strip().splitlines()[-1] == "20", stdout[-2000:]


@pytest.mark.asyncio(loop_scope="module")
async def test_pymanopt_autograd(agent_env: SandboxEnvironment) -> None:
    # Minimising x^T diag(1,2,3) x on the unit sphere: the smallest eigenvalue, 1.
    script = (
        "import autograd.numpy as anp\n"
        "import pymanopt\n"
        "from pymanopt.manifolds import Sphere\n"
        "from pymanopt.optimizers import SteepestDescent\n"
        "manifold = Sphere(3)\n"
        "@pymanopt.function.autograd(manifold)\n"
        "def cost(x):\n"
        "    return anp.sum(x**2 * anp.array([1.0, 2.0, 3.0]))\n"
        "result = SteepestDescent(verbosity=0).run(pymanopt.Problem(manifold, cost))\n"
        "assert abs(result.cost - 1.0) < 1e-3, result.cost\n"
        "print('ok')\n"
    )
    code, stdout, stderr = await _bash(
        agent_env, f"python3 - <<'EOF'\n{script}EOF", timeout=300
    )
    assert code == 0, f"pymanopt/autograd failed:\n{stderr[-2000:]}\n{stdout[-2000:]}"


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
    # The baked depot (at Julia's default /root/.julia) must load offline with
    # no re-precompilation surprises.
    code, stdout, stderr = await _bash(
        agent_env,
        "julia -e 'using Oscar; println(order(symmetric_group(4)))'",
        timeout=600,
    )
    assert code == 0, f"julia/Oscar failed:\n{stderr[-2000:]}"
    assert stdout.strip().endswith("24")


@pytest.mark.asyncio(loop_scope="module")
async def test_loogle_finds_nat_prime(agent_env: SandboxEnvironment) -> None:
    # Upstream's documented invocation (its README ships at
    # /usr/local/share/doc/loogle): from the project, via `lake env`. The
    # Mathlib index is prebuilt in the image, so this must not fall into the
    # slow index-construction path -- but cold start still imports Mathlib,
    # hence the generous timeout.
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


@pytest.mark.asyncio(loop_scope="module")
async def test_lake_builds_multi_module_submission(agent_env: SandboxEnvironment) -> None:
    """The multi-file submission contract in the agent image: `Submission` is a
    registered Lake library (apn/lean/Dockerfile), so a `Spec.lean` importing a
    helper module beside it builds with `lake build Submission.Spec` -- the
    command the prompt advertises -- and the helper's olean lands in .lake at
    the module path Lake derives from the file path."""
    helper = (
        "import Mathlib.Tactic\n"
        "theorem smoke_aux (a b : Nat) : a + b = b + a := by omega\n"
    )
    spec = (
        "import Submission.SmokeHelpers.Aux\n"
        "theorem smoke_tgt : 1 + 2 = 2 + 1 := smoke_aux 1 2\n"
    )
    await agent_env.write_file(f"{SUBMISSION_DIR}/SmokeHelpers/Aux.lean", helper)
    await agent_env.write_file(f"{SUBMISSION_DIR}/Spec.lean", spec)
    try:
        code, stdout, stderr = await _bash(
            agent_env, "cd /workspace/leanproject && lake build Submission.Spec", timeout=900
        )
        assert code == 0, f"lake build Submission.Spec failed:\n{stderr[-2000:]}\n{stdout[-2000:]}"
        code, stdout, stderr = await _bash(
            agent_env,
            "cd /workspace/leanproject && find .lake/build/lib -path '*/Submission/SmokeHelpers/Aux.olean'",
        )
        assert code == 0 and stdout.strip(), f"helper olean not built:\n{stderr[-2000:]}"
    finally:
        await agent_env.exec(
            ["rm", "-rf", f"{SUBMISSION_DIR}/SmokeHelpers", f"{SUBMISSION_DIR}/Spec.lean"]
        )
