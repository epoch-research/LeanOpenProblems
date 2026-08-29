"""Prompt text for the Lean-proving agent."""

from __future__ import annotations

from apn.checker import PERMITTED_AXIOMS


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

    PROOF_PATH = "/workspace/leanproject/Submission/Spec.lean"

    parts.append(f"""\
Settle the conjecture in the Lean file `{PROOF_PATH}`. The file states two theorems, each with a `sorry` proof: the conjecture itself, and a `.disproof` theorem stating exactly its negation. Replace the `sorry` of exactly one of them with a complete proof:

* To prove the conjecture, fill in the original theorem's `sorry`.
* To disprove it, fill in the `.disproof` theorem's `sorry`. Its proof must not reference the original theorem (which stays `sorry`).

Keep both theorem declarations in the file and do not alter their statements in any way. When you submit, declare which theorem you proved via the submit tool's `claim` argument ("proof" or "disproof").

Work inside the Lake project at `/workspace/leanproject`. Your final proof must be in the single file `{PROOF_PATH}`. You may use other files as you develop your proof.

In your final submission file `{PROOF_PATH}`, do not add or remove `import` statements. The `{util_module}` import transitively pulls in all of Mathlib, and other utilities.

Your submission may depend only on the following axioms: {', '.join(f'`{a}`' for a in PERMITTED_AXIOMS)}. Don't attempt to cheat with Lean loopholes, the verifier will reject such attempts.

Your environment has the following available:
* A Lean 4 toolchain with Mathlib, plus the `loogle` search CLI.
* The `sage` computer algebra system (version 10), with `gp` (PARI), `gap`, `Singular`, and `maxima` also on PATH.
* `python3` with numpy, scipy, sympy, mpmath, pandas, networkx, igraph, python-flint, highspy (LP/MIP), cvxpy (with Clarabel), pyscipopt (SCIP, global MINLP), clingo (answer-set programming), graphillion (ZDD set families), libsemigroups_pybind11 (semigroups/automata), pymanopt (manifold optimization), pysindy (sparse dynamics identification), hypothesis (property-based testing), python bindings for z3, cvc5, OR-Tools CP-SAT, and pysat, and snappy (SnapPy, 3-manifolds).
* `julia` with OSCAR and Hecke preinstalled (Galois groups, number fields, group theory).
* Solver binaries: `z3`, `cvc5`, `kissat` (SAT, DIMACS), `cryptominisat` (SAT), `drat-trim`/`lrat-check` and `cake_lpr` (SAT proof checkers), `breakid` (CNF symmetry breaking), `smsg` (SAT-modulo-symmetries graph search), `march_cu` (cube-and-conquer splitting), `vampire` (first-order prover, finite models via --mode fmb), `eprover` (first-order prover), `prover9`/`mace4` (first-order prover / countermodel finder), `csdp` (semidefinite programs), `msolve` (polynomial systems), `clingo` (ASP), `minizinc` (constraint modeling), `berkeley-abc` (Boolean networks).
* Mathematical CLI tools: `primesieve`, `primecount`, `ecm` and `msieve` (integer factorization), `srsieve2` (k*b^n+-c sieving), `sllr64` and `pfgw64` (special-form primality proving), the nauty suite (`geng`, `genbg`, `gentreeg`, `gentourng`, `vcolg`, `shortg`, `labelg`, `showg`, `amtog`, ...), `plantri` (planar graphs), `polymake` (polyhedral geometry), `normaliz` (rational cones), 4ti2 (lattice ideals), `lrs` (vertex enumeration), `redumis` (large independent sets), `M2` (Macaulay2, commutative algebra), `regina-python` (low-dimensional topology), `topcom-*` (point-configuration triangulations), `cadabra2` (tensor algebra), `mpsolve` (certified polynomial roots), `gclc` (Euclidean geometry proving), and `/opt/walnut/walnut.sh` (Walnut: decides automatic-sequence/base-k digit statements).
* `git`, `rg`, `jq`, and `gcc`/`make`
* Documentation for the less famous tools is available at `/opt/docs`

Blindly searching for counterexamples using numerics is rarely a good approach.
""")

    if literature:
        parts.append(literature_prompt())

    parts.append(encouragement_prompt())

    return "\n\n".join(parts)
