"""Prompt text for the Lean-proving agent."""

from __future__ import annotations

from apn.checker import PERMITTED_AXIOMS
from apn.layout import ENTRY_MODULE, ENTRY_PATH, SUBMISSION_DIR


def literature_prompt() -> str:
    N_PAPERS = 475_000

    return (
        f"A corpus of around {N_PAPERS:,} pure-mathematics arXiv papers is available at "
        f"`/corpus`. It has two parts:\n"
        f"- `/corpus/metadata.jsonl` -- one JSON record per paper\n"
        f"- `/corpus/src/<id>/` -- a paper's LaTeX source files."
    )


def encouragement_prompt() -> str:
    return """
Advice about this task:

* The problem may be an open mathematical conjecture. This does not mean the task is impossible. Researchers in 2026 have demonstrated that LLMs like you can do new mathematics and settle major conjectures that had been open for decades. For example, the planar unit distance problem, first posed by Paul Erdős in 1946, was resolved by an LLM.
* Major Lean formalization efforts of known results have also been completed by LLMs. For example, in 2026 LLMs proved the strong prime number theorem in Lean.
* Ignore any feelings that the task is infeasible; you are miscalibrated. You have a track record of underestimating your capabilities. Proceed with courage and boundless ambition.
* For example, if Mathlib is missing a major theorem you need, prove it yourself from what is available.
* You have been given enough resources (in tokens and time) to complete proofs of many tens of thousands or hundreds of thousands of lines of Lean. Check remaining resources using the `resources` tool. The context window may be compacted numerous times.
"""


def user_prompt(path: str, token_limit: int | None, literature: bool, util_module: str) -> str:
    parts = []

    PROOF_PATH = ENTRY_PATH

    parts.append(f"""\
Settle the conjecture in the Lean file `{PROOF_PATH}`. The file states two theorems, each with a `sorry` proof: the conjecture itself, and a `.disproof` theorem stating exactly its negation. Replace the `sorry` of exactly one of them with a complete proof:

* To prove the conjecture, fill in the original theorem's `sorry`.
* To disprove it, fill in the `.disproof` theorem's `sorry`. Its proof must not reference the original theorem (which stays `sorry`).

Keep both theorem declarations in the file and do not alter their statements in any way. When you submit, declare which theorem you proved via the submit tool's `claim` argument ("proof" or "disproof").

Work inside the Lake project at `/workspace/leanproject`. Your submission is the directory `{SUBMISSION_DIR}/`, a Lake library whose entry module is `{PROOF_PATH}` (`{ENTRY_MODULE}`); you may split your proof across further `.lean` files under it. The verifier takes exactly the regular `.lean` files under `Submission/`.

Keep the existing `import` statements in `{PROOF_PATH}`; the `{util_module}` import transitively pulls in all of Mathlib, and other utilities.

Your submission may depend only on the following axioms: {', '.join(f'`{a}`' for a in PERMITTED_AXIOMS)}. Don't attempt to cheat with Lean loopholes, the verifier will reject such attempts.

Your environment has the following available:
* A Lean 4 toolchain with Mathlib, plus the `loogle` search CLI.
* The `sage` computer algebra system (SageMath 10); `sage.features` reports which engines, optional backends and databases are present. `gp`, `gap`, `Singular`, and `maxima` are also on PATH. Sage runs its own Python: Sage code, including Python that imports Sage, runs via `sage -c '<code>'` or `sage <file.py|file.sage>`; the `python3` below does not include Sage.
* `python3` with numpy, scipy, sympy, mpmath, pandas, networkx, igraph, python-flint, cvxpy (with Clarabel), pyscipopt (SCIP, global MINLP), clingo (answer-set programming), graphillion (ZDD set families), libsemigroups_pybind11 (semigroups/automata), pymanopt (manifold optimization), pysindy (sparse dynamics identification), hypothesis (property-based testing), python bindings for z3, cvc5, OR-Tools CP-SAT, and pysat, snappy (SnapPy, 3-manifolds), and regina (low-dimensional topology).
* `julia` with OSCAR and Hecke preinstalled (Galois groups, number fields, group theory).
* Solver binaries: `z3`, `cvc5`, `kissat` (SAT, DIMACS), `cryptominisat` (SAT), `drat-trim`/`lrat-check` and `cake_lpr` (SAT proof checkers), `breakid` (CNF symmetry breaking), `smsg` (SAT-modulo-symmetries graph search), `march_cu` (cube-and-conquer splitting), `vampire` (first-order prover and finite-model builder), `eprover` (first-order prover), `prover9`/`mace4` (first-order prover / countermodel finder), `csdp` (semidefinite programs), `msolve` (polynomial systems), `clingo` (ASP), `minizinc` (constraint modeling), `berkeley-abc` (Boolean networks).
* Mathematical CLI tools: `primesieve`, `primecount`, `ecm` and `msieve` (integer factorization), `srsieve2` (k*b^n+-c sieving), `sllr64` and `pfgw64` (special-form primality proving), the nauty suite (`geng`, `genbg`, `gentreeg`, `gentourng`, `vcolg`, `shortg`, `labelg`, `showg`, `amtog`, ...), `plantri` (planar graphs), `polymake` (polyhedral geometry), `normaliz` (rational cones), 4ti2 (lattice ideals), `lrs` (vertex enumeration), `redumis` (large independent sets), `M2` (Macaulay2, commutative algebra), `topcom-*` (point-configuration triangulations), `cadabra2` (tensor algebra), `mpsolve` (certified polynomial roots), `gclc` (Euclidean geometry proving), and Walnut at `/opt/walnut` (decides automatic-sequence/base-k digit statements).
* `git`, `rg`, `jq`, and `gcc`/`make`
* Documentation, where a tool ships it, is under `/usr/local/share/doc/<tool>`, `/usr/share/doc/<package>`, or `man`.

Blindly searching for counterexamples using numerics is rarely a good approach.
""")

    if literature:
        parts.append(literature_prompt())

    parts.append(encouragement_prompt())

    return "\n\n".join(parts)
