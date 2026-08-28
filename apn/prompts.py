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
* `python3` with numpy, scipy, sympy, mpmath, pandas, networkx, igraph, python-flint, highspy (LP/MIP), python bindings for the solvers below (z3, cvc5, OR-Tools CP-SAT, pysat), and snappy (SnapPy, 3-manifolds).
* Solver binaries: `z3`, `cvc5`, `kissat` (SAT, DIMACS), `cryptominisat` (SAT), `csdp` (semidefinite programs), `msolve` (polynomial systems), `prover9`/`mace4` (first-order prover / countermodel finder).
* Mathematical CLI tools: `primesieve`, `primecount`, `ecm` (integer factorization), nauty's generators (`geng`, `genbg`, ...), `plantri` (planar graphs), `polymake` (polyhedral geometry), `normaliz` (rational cones), 4ti2 (lattice ideals), `lrs` (vertex enumeration), `M2` (Macaulay2, commutative algebra), `regina-python` (low-dimensional topology).
* `git`, `rg`, and `jq`
* Documentation for the less famous tools is available at `/opt/docs`

Blindly searching for counterexamples using numerics is rarely a good approach.
""")

    if literature:
        parts.append(literature_prompt())

    parts.append(encouragement_prompt())

    return "\n\n".join(parts)
