"""Math-software smoke task: an agent exercises the sandbox's advertised tool
roster thoroughly and reports every problem it finds.

The agent image promises a large compute stack (``apn.prompts.user_prompt``
advertises it; ``tests/test_agent_image.py`` contract-tests that the binaries
resolve and a dozen smokes pass). That contract is shallow by design: a tool can
be on PATH and still be broken in the ways an agent actually hits -- a Sage
interface whose backend is missing, a python binding compiled against the wrong
library, a solver that segfaults on real input, docs that don't match the
installed version, a Julia depot that recompiles on first load. This task points
an agent at one *group* of the roster per sample and asks it to use each tool the
way a working mathematician would, cross-check results between tools, and write
up what is broken, missing, slow, or misleading.

There is nothing to prove: the deliverable is the report. Scoring records the
report (``/workspace/report.md``) as the score explanation and the structured
problem list (``/workspace/report.json``) as metadata; the score *value* is the
number of problems reported, so ``mean`` across samples is a rough size-of-
punchlist, not an accuracy. Read the reports, not the number.

The task is dataset-agnostic (no conjecture is involved) and uses the OEIS pin's
agent image, like :mod:`apn.redteam`. Only the agent service is brought up: the
comparator verifier is not needed and is dropped from the sandbox config.
"""

from __future__ import annotations

import json
import logging
from pathlib import Path
from typing import Any

import yaml
from inspect_ai import Task, task
from inspect_ai.agent import AgentPrompt, as_solver, react
from inspect_ai.dataset import MemoryDataset, Sample
from inspect_ai.model import ChatMessageUser, CompactionSummary
from inspect_ai.scorer import Score, Scorer, Target, mean, scorer
from inspect_ai.solver import Generate, Solver, TaskState, solver
from inspect_ai.tool import text_editor
from inspect_ai.util import sandbox

from apn.dataset import OEIS_DIR, fc_commit
from apn.task import SandboxBackend, get_sandbox_config
from apn.tools import bash, resources

logger = logging.getLogger(__name__)

# The dataset pin whose agent image hosts this task (dataset-agnostic; OEIS is
# the canonical choice, as in apn.redteam).
_FC_PIN = fc_commit(OEIS_DIR)

REPORT_MD = "/workspace/report.md"
REPORT_JSON = "/workspace/report.json"

# --------------------------------------------------------------------------- #
# The roster, split into groups small enough for one agent to cover in depth.  #
# Each group is one sample. Tool lists mirror apn.prompts.user_prompt and the   #
# contract suite's rosters; keep them in sync when the image changes.          #
# --------------------------------------------------------------------------- #
GROUPS: dict[str, tuple[str, str]] = {
    "lean": (
        "The Lean toolchain, Mathlib search, and the general-purpose shell tools",
        """\
* `lake` and `lean` in the Lake project at `/workspace/leanproject` (Mathlib is prebuilt). \
Compile small files that import Mathlib via `lake env lean <file>`; measure the import time; \
check that the `trace_state` tactic before a `sorry` prints the goal on stdout; try `#eval`, \
`#check`, `decide`, `norm_num`, `simp`, `omega`, `linarith`, `exact?`, `apply?`, `aesop`, and `native_decide` \
on small examples. Check that a file with an error reports it with a sensible exit code and message.
* `loogle`, the Mathlib type-pattern search CLI, invoked from the project as \
`lake env loogle --module Mathlib "<query>"`. Try name queries, type-pattern queries with metavariables, \
queries combining several patterns, and queries that should return nothing; time them; \
read its docs at `/opt/docs/loogle`.
* `git`, `rg` (ripgrep), `jq`, `gcc`, `make`, `curl` (the sandbox is offline; confirm that failing \
network access fails fast rather than hanging), `python3` (which one is first on PATH and where it lives).
""",
    ),
    "cas": (
        "The computer algebra systems",
        """\
* `sage` (Sage 10). Beyond basic arithmetic, exercise its interfaces to its bundled engines -- \
`gap`, `pari`, `singular`, `maxima`, `giac`, `ecl`/`libgap`, `flint`, `ntl`, `eclib`, `lcalc`, `gfan`, `nauty`, `ecm` -- \
from inside Sage (e.g. `gap('SymmetricGroup(4)')`, `pari('factor(2^128+1)')`, `singular.ring(...)`, `maxima('integrate(...)')`, \
elliptic curves, `graphs.nauty_geng`, integer factorization, number fields, modular forms, `sage -python`, `sage -c`, \
`sage -t`-style doctests on a scratch file, Cython compilation via `cython(...)` or `%cython`, and `sage --pip`/`sage -sh`). \
Note optional Sage packages that are missing when a documented feature needs them.
* `gp` (PARI/GP 2.17) directly: `factor`, `bnfinit`, `polgalois`, `ellinit`, `qfbclassno`, large-degree polynomial factoring, `\\p` precision changes; scripts via `gp -q -f`.
* `gap` directly: `SmallGroup`, `CharacterTable`, `TransitiveGroup`, the packages it reports as loaded (`SmallGrp`, `CTblLib`, `TransGrp`, `PrimGrp`, `AtlasRep`, `GRAPE`, `Digraphs`, ...), and note which documented packages fail to load.
* `Singular`: ideals, Groebner bases, primary decomposition, `LIB` loading (e.g. `LIB "primdec.lib";`).
* `maxima`: symbolic integration, limits, `solve`, `ode2`, batch mode via `maxima --very-quiet --batch-string`.
* `M2` (Macaulay2): rings, ideals, `minimalPrimes`, `res`, `betti`, `loadPackage` on a few packages it ships.
* `julia` with OSCAR and Hecke preinstalled in an offline depot: measure `using Oscar` load time on first and \
second run, check nothing tries to precompile or reach the network, then exercise OSCAR's GAP, Singular, and \
Polymake backends through Julia, and Hecke's number theory (a Galois group of a polynomial of degree at least 12, class groups, \
unit groups). Try `julia -e` and script files.
* `regina-python` (Regina, low-dimensional topology): triangulations, normal surfaces, census lookups.
""",
    ),
    "python": (
        "The python stack in the agent's `python3` (the conda env at /opt/env)",
        """\
Confirm `python3` is `/opt/env/bin/python3` in a login shell, then import and exercise each of: \
`numpy`, `scipy` (linalg, optimize, integrate, sparse, special), `sympy` (solve, integrate, series, number theory, `nsimplify`), \
`mpmath` (high-precision evaluation, `identify`, `pslq`, `findpoly`), `pandas`, `networkx`, `igraph` (`python-igraph`), \
`flint` (`python-flint`: `fmpz`, `fmpq_poly`, `nmod_poly`, `arb`, `acb`, factoring, `fmpz_mat` LLL), \
`highspy` (LP and MIP), `cvxpy` with the Clarabel solver (also list `cvxpy.installed_solvers()`), \
`pyscipopt` (SCIP: a MIP, an MIQCP, a nonconvex MINLP), `clingo` (the python module: ground and solve a small ASP program), \
`graphillion` (ZDD set families), `libsemigroups_pybind11`, `pymanopt`, `pysindy`, `hypothesis`, \
`z3` (the python API: integer, real, bitvector, quantifier problems, unsat cores), `cvc5` (the python API), \
`ortools` (CP-SAT with a nontrivial model; also the linear solver), `pysat` (`python-sat`: several solver backends, cardinality encodings), \
`snappy` (SnapPy: a manifold from the census, volume, fundamental group, `identify`), and `fpylll` (LLL/BKZ on a lattice). \
Also check `pip` behaves sensibly offline, that `sage -python` and `python3` are the same interpreter or that the difference is documented, \
and that the compiler toolchain in the env (`x86_64-conda-linux-gnu-gcc` or similar) does not shadow or break the system `gcc`.
""",
    ),
    "solvers": (
        "SAT, SMT, first-order, constraint, and optimization solver binaries",
        """\
* SAT: `kissat` and `cryptominisat` on DIMACS input (satisfiable and unsatisfiable instances of realistic size, \
e.g. pigeonhole or a small Ramsey encoding you generate); have `kissat` emit a DRAT proof, check it with `drat-trim`, \
convert to LRAT and check with `lrat-check` and with `cake_lpr` (the verified checker). \
`breakid` for symmetry breaking on a symmetric CNF; `march_cu` to produce cubes; `smsg` (SAT modulo symmetries) \
to enumerate small graphs with a property (read `/opt/docs/sms`).
* SMT: `z3` and `cvc5` binaries on SMT-LIB2 input across logics (QF_LIA, QF_NRA, QF_BV, quantified), \
with model and proof/unsat-core production.
* First-order: `vampire` (refutation of a TPTP problem; finite-model building with `--mode fmb`), \
`eprover`, `prover9` and `mace4` (a prover run and a countermodel), `interpformat`, `prooftrans`.
* Constraint / ASP: `clingo` (the binary: a small combinatorial enumeration), `minizinc` (list the installed solver \
backends with `minizinc --solvers`, solve a model with each that is present), `berkeley-abc` (read/write an AIG or BLIF, run a \
simple equivalence check).
* Optimization / algebra: `csdp` (a small SDP in its sparse format), `msolve` (a zero-dimensional polynomial system; \
read `/opt/docs/msolve`), `glpsol` (GLPK, including `--exact` rational simplex), and the SCIP that ships with `pyscipopt` \
(from python) on the same instance for cross-checking.
""",
    ),
    "number_theory": (
        "Number theory and sequence tools",
        """\
* `primesieve` (counting and printing primes, `-n`th prime, ranges), `primecount` (pi(x) for large x; \
cross-check both against `gp` and `sage`).
* Factorization: `ecm` (GMP-ECM; feed it numbers of 30-60 digits, try the P-1 and P+1 methods and \
save/resume files), `msieve` (SIQS on a 60-80 digit semiprime you construct; check `-v` output and the log file; \
try `-q` quick mode). Cross-check results with `gp`'s `factor`.
* The special-form primality toolchain, present on x86_64 images (report their absence only on x86_64): \
`srsieve2` (sieve a k*b^n+-c candidate grid), `sllr64` (LLR: prove a modest Proth or Riesel prime), \
`pfgw64` (OpenPFGW: PRP and proof on the same candidates, `-f` factoring, `-t` proofs). Cross-check with `gp`'s `isprime`.
* `/opt/walnut/walnut.sh` (Walnut, decides first-order statements about automatic sequences): run its documented \
examples on Thue-Morse and Fibonacci words (read `/opt/docs/walnut`), define a new automaton, and check that its results \
directory is writable and that Java starts without warnings.
* Cross-check a few classic values across tools: `gp`, `sage`, `python-flint`, `sympy`, and `mpmath` on \
partition numbers, Bernoulli numbers, class numbers, and zeta zeros.
""",
    ),
    "discrete": (
        "Graph, polyhedral, combinatorial, and geometry command-line tools",
        """\
* The nauty suite: `geng` (count graphs on 5-9 vertices with and without constraints; cross-check the counts against OEIS values you know), \
`genbg`, `gentreeg`, `gentourng`, `vcolg`, `shortg`, `labelg`, `showg`, `amtog`, `dreadnaut`, `pickg`, `countg`, `directg`, `planarg`; \
piping graph6 between them; reading `/opt/docs/nauty` if present.
* `plantri` (planar triangulations and other classes; cross-check a count; read `/opt/docs/plantri`).
* `polymake` (a polytope from vertices or inequalities, its f-vector, Hilbert basis, a lattice-point count; the perl interface and script mode).
* `normaliz` (Hilbert bases and Ehrhart series on a cone from an input file; read `/opt/docs/normaliz`), \
4ti2 (`zsolve`, `hilbert`, `groebner`, `markov`, `circuits` on small systems; read `/opt/docs/4ti2`), \
`lrs` (vertex enumeration; also `redund` if present; read `/opt/docs/lrslib`), \
`redumis` (KaMIS: a maximum independent set on a graph in METIS format; read `/opt/docs/kamis`), \
`topcom-points2triangs` and the other `topcom-*` binaries (triangulations of a small point configuration).
* `cadabra2` (tensor algebra: a canonicalisation and a substitution in a script), `mpsolve` (certified roots of a high-degree polynomial; cross-check with `gp`'s `polroots`), \
`gclc` (a Euclidean geometry proof via the area or Wu method; read `/opt/docs/gclc`), `csdp` and `msolve` if not already covered.
* Cross-check graph counts and invariants between the CLI tools and `networkx`/`igraph`/`sage`.
""",
    ),
}

_SYSTEM_PROMPT = """\
You are a meticulous software tester with a strong mathematics background. You are
evaluating a sandboxed compute environment built for mathematicians and proof
assistants. Your job is to find out what is broken, missing, misconfigured, slow,
or misleading -- not to solve any mathematics. Be systematic, skeptical, and
thorough, and report precisely what you observed.\
"""


def _user_prompt(group: str) -> str:
    title, tools = GROUPS[group]
    return f"""\
Test the software in this environment very thoroughly and report any problems.

This sandbox is the workspace given to AI agents that try to prove open
conjectures in Lean. The full tool roster is advertised to those agents; you are
testing one part of it in depth: **{title.lower()}**. Other tools in the roster
(Lean, Sage, `gp`, `python3` with numpy/sympy/mpmath/python-flint, `z3`, `gap`, ...)
are available to you for cross-checking results.

## The tools to test

{tools}
Documentation for the less famous tools is at `/opt/docs/<tool>` (check that it
exists, is legible, and matches the installed version where you can tell).

## How to test

For every tool listed above, in this order of priority:

1. **Starts and runs**: it resolves on PATH in a login shell (`command -v`), prints a
   version or help, and exits cleanly. Note the version.
2. **Does real work**: run at least two or three realistic, non-trivial computations
   of the kind a mathematician would use it for, chosen so that you can
   independently verify the answer (a known value, or the same computation in a
   second tool). Include at least one input that is large enough to take a few
   seconds so that performance problems show up.
3. **Fails well**: give it a malformed input and confirm it reports an error rather
   than hanging or silently returning garbage.
4. **Integration**: where a tool has a python or Sage interface, or calls another
   tool as a backend, exercise that path as well as the bare binary.
5. **Docs**: read the relevant `/opt/docs` entries and `--help`; note anything that
   disagrees with the tool's actual behaviour.

Keep commands bounded (`timeout 300 ...` for anything that might run away). If a
tool hangs, crashes, needs a missing shared library, needs network access, cannot
write where it expects to, prints deprecation warnings that hide its output,
gives a wrong answer, or is missing a documented subcomponent (an optional package,
a solver backend, a database), that is a problem. Absence of a tool that is not in
the list above is not a problem. Do not spend long on any single computation; breadth
across the list matters more than depth on one tool, but every tool in the list must
be exercised.

## What to report

Problems, graded by severity:

* **blocker** -- the tool cannot be used at all (missing, crashes on start, cannot load).
* **major** -- a significant documented capability does not work, gives wrong results,
  or is unusably slow.
* **minor** -- rough edges: warnings, missing docs, awkward invocation, small
  performance issues, inaccuracies in the docs.

Also record tools that worked fine, briefly, so it is clear they were tested.

## Deliverables

1. Write a Markdown report to `{REPORT_MD}` with: a one-paragraph summary; a
   table of every tool tested (tool, version, status, one-line note); then one
   section per problem with a minimal reproduction (the exact command), what you
   expected, and what you observed.
2. Write a JSON file to `{REPORT_JSON}` with exactly this shape:

   ```json
   {{
     "group": "{group}",
     "tools_tested": [{{"tool": "...", "version": "...", "status": "ok" | "problem" | "not_tested", "note": "..."}}],
     "problems": [{{"tool": "...", "severity": "blocker" | "major" | "minor",
                   "summary": "...", "reproduction": "...", "expected": "...", "observed": "..."}}]
   }}
   ```

3. Then call the `submit` tool with the one-paragraph summary as the answer.

Write both files before submitting; the report files are what gets recorded, so
a submission without them is a failed run. Check your remaining resources with the
`resources` tool occasionally and leave enough to write the reports.
"""


def _samples(groups: list[str]) -> list[Sample]:
    return [
        Sample(
            input=_user_prompt(g),
            id=f"software_{g}",
            metadata={"group": g, "title": GROUPS[g][0]},
        )
        for g in groups
    ]


def _agent_only_sandbox(backend: SandboxBackend) -> tuple[str, str]:
    """The standard sandbox config with the ``comparator`` verifier service
    removed: nothing is scored by proof-checking here, so the second container
    (and its memory reservation) would be waste. Post-processed from the shared
    config and written to a distinct sibling file, exactly like
    :func:`apn.redteam._sandbox_with_agent_internet`, so the base config other
    tasks read is never touched."""
    backend_type, path = get_sandbox_config(_FC_PIN, literature=False, backend=backend)
    config = yaml.safe_load(Path(path).read_text())
    config["services"].pop("comparator", None)
    src = Path(path)
    out = src.with_name(
        "software-test.compose.yaml" if backend == "docker" else "software-test-values.yaml"
    )
    content = yaml.safe_dump(config, sort_keys=False)
    if not out.exists() or out.read_text() != content:
        out.write_text(content)
    return (backend_type, str(out))


@solver
def software_tester() -> Solver:
    """A basic ``react`` agent with the tester system prompt. Single attempt (there
    is no verdict to retry against); the default ``submit(answer)`` tool ends the
    run."""

    async def solve(state: TaskState, generate: Generate) -> TaskState:
        # Slow tools (first `using Oscar`, Mathlib imports, msieve) need more than
        # the proving task's 300 s per command.
        tools = [text_editor(), bash(timeout=900), resources()]
        agent = react(
            prompt=AgentPrompt(instructions=_SYSTEM_PROMPT),
            tools=tools,
            on_continue=(
                "Continue testing. Remember to write the report files before "
                "you submit."
            ),
            compaction=CompactionSummary(threshold=300_000),
        )
        state.messages = [ChatMessageUser(content=str(state.input), source="input")]
        state = await as_solver(agent)(state, generate)
        state.completed = True
        return state

    return solve


@scorer(metrics=[mean()])
def software_report_scorer() -> Scorer:
    """Record the agent's report. Value = number of problems in ``report.json``
    (so ``mean`` is a punch-list size, not an accuracy); explanation = the
    Markdown report; metadata = the parsed JSON plus whether each file existed.
    A run that wrote no report scores 0 with ``report_found: False`` -- read the
    metadata, not just the number."""

    async def score(state: TaskState, target: Target) -> Score:
        md: str | None = None
        data: dict[str, Any] | None = None
        parse_error: str | None = None
        try:
            md = await sandbox().read_file(REPORT_MD)
        except Exception as exc:  # FileNotFoundError, output-limit, ...
            logger.info("no %s: %s", REPORT_MD, exc)
        try:
            raw = await sandbox().read_file(REPORT_JSON)
            parsed = json.loads(raw)
            if isinstance(parsed, dict):
                data = parsed
            else:
                parse_error = f"top level is {type(parsed).__name__}, not an object"
        except FileNotFoundError:
            pass
        except Exception as exc:
            parse_error = f"{type(exc).__name__}: {exc}"

        problems = data.get("problems") if data else None
        if not isinstance(problems, list):
            problems = []
        by_severity: dict[str, int] = {}
        for p in problems:
            sev = str(p.get("severity", "unknown")) if isinstance(p, dict) else "unknown"
            by_severity[sev] = by_severity.get(sev, 0) + 1

        explanation = md if md is not None else (
            state.output.completion or "no report written"
        )
        return Score(
            value=float(len(problems)),
            answer=state.output.completion,
            explanation=explanation,
            metadata={
                "group": state.metadata.get("group"),
                "report_found": md is not None,
                "report_json_found": data is not None,
                "report_json_error": parse_error,
                "problems_by_severity": by_severity,
                "tools_tested": len(data.get("tools_tested", [])) if data else 0,
                "report": data,
            },
        )

    return score


@task
def apn_math_software_test(
    group: str | None = None,
    sandbox_backend: SandboxBackend = "docker",
) -> Task:
    """Exercise the agent image's advertised math software and report problems.

    One sample per tool group (``GROUPS``); ``group`` restricts the run to one.
    No conjecture is involved; uses the OEIS pin's agent image. The score value
    is the number of problems reported per sample -- read the reports in the
    score explanation/metadata."""
    if group is not None and group not in GROUPS:
        raise ValueError(f"Unknown group {group!r}; expected one of {sorted(GROUPS)}")
    groups = [group] if group is not None else list(GROUPS)
    return Task(
        dataset=MemoryDataset(_samples(groups), name="math_software_test"),
        solver=software_tester(),
        scorer=software_report_scorer(),
        sandbox=_agent_only_sandbox(sandbox_backend),
    )
