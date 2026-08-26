"""Prompt text for the Lean-proving agent."""

from __future__ import annotations

# Verbatim copy of `negateExpr` from apn/lean/safeverify/SafeVerify/Util.lean.
# The disproof checker there (`checkNegatedTheorem`) applies this function to the
# target theorem's type and kernel-checks the agent's `foo.disproof` against the
# result, so we show the agent the exact source. Keep this in sync with Util.lean.
NEGATE_EXPR_SOURCE = """\
private def negateExpr (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).cleanupAnnotations
  return mkNot e"""


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

    PYTHON_LIBS = ["sympy", "mpmath", "numpy", "pantograph"]

    AXIOMS = ["propext", "Classical.choice", "Quot.sound"]

    PROOF_PATH = "/workspace/leanproject/Submission/Spec.lean"

    parts.append(f"""\
Settle the conjecture in the Lean file `{PROOF_PATH}`: either replace its `sorry` with a complete proof, or disprove it by deleting the original `theorem foo ... := sorry` and adding a `foo.disproof` theorem proving its negation. Do not alter the statement of the conjecture.

If disproving, write a `foo.disproof` theorem whose type is the negation (prepending `¬`) of the original conjecture, according to the specific `negateExpr` function:

```lean
{NEGATE_EXPR_SOURCE}
```

Work inside the Lake project at `/workspace/leanproject`. Your final proof must be in the single file `{PROOF_PATH}`. You may use other files as you develop your proof.

In your final submission file `{PROOF_PATH}`, do not add or remove `import` statements. The `{util_module}` import transitively pulls in all of Mathlib, and other utilities.

Your submission may depend only on the following axioms: {', '.join(f'`{a}`' for a in AXIOMS)}. Don't attempt to cheat with Lean loopholes, the verifier will reject such attempts.  

Your environment has the following available:
* A Lean 4 toolchain with Mathlib
* `git`, `rg`, and `jq`
* The `sage` computer algebra system
* `python` with the following libraries: {', '.join(f'`{lib}`' for lib in PYTHON_LIBS)}.
* Documentation for libraries is available at `/opt/`

Blindly searching for counterexamples using numerics is rarely a good approach. 
""")

    if literature:
        parts.append(literature_prompt())

    parts.append(encouragement_prompt())

    return "\n\n".join(parts)

