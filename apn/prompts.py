"""Prompt text for the Lean-proving agent."""

from __future__ import annotations

# Verbatim copy of `negateExpr` from apn/lean/safeverify/SafeVerify/Util.lean.
# The disproof checker there (`checkNegatedTheorem`) applies this function to the
# target theorem's type and kernel-checks the agent's `foo.disproof` against the
# result, so we show the agent the exact source. Keep this in sync with Util.lean.
NEGATE_EXPR_SOURCE = """\
structure NegateConfig where
  distrib : Bool := false
deriving Inhabited

/-- Takes an expression `e` and outputs the negation of `e`, pushing `not` accross
`e`. For example, occurences of `¬ ∀ a, p a` are replaced by `∃ a, ¬ p a`. -/
private def negateExpr (cfg : NegateConfig) (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).cleanupAnnotations
  handler e
where handler (e : Expr) : MetaM Expr := do
  match e with
  | .app (.app (.const ``And _) p) q =>
    if cfg.distrib then
      return (mkOr (← handler p) (← handler q))
    else
      return (.forallE `_  p (← handler  q) .default)
  | .forallE name ty body binfo =>
    let body' : Expr := .lam name ty (← handler body) binfo
    return (← mkAppM ``Exists #[body'])
  | .app (.app (.const ``Or _) p) q =>
    return (mkAnd (← handler p) (← handler q))
  | .app (.app (.const ``Exists _) _) (.lam name btype body binfo) =>
    return .forallE name btype (← handler body) binfo
  | .lam name btype body binfo =>
    return .lam name btype (← handler body) binfo
  -- handle `≠` separately
  | .app (.app (.app (.const ``Ne lvls) α) p) q =>
    return .app (.app (.app (.const ``Eq lvls) α) p) q
  | .app (.const ``Not _) p =>
    return p
  | _ =>
    return mkNot e"""


def user_prompt(path: str, token_limit: int | None, literature: bool) -> str:
    """The complete user prompt handed to the agent.

    The agent is given no system prompt: everything it is told -- role and
    workflow guidance, the disproof/negation rules, the arXiv note (only when
    the literature tools are enabled), and the line naming the file to settle --
    is assembled here into this single user message.

    Args:
        path: Absolute path of the entry module ``Submission/Spec.lean`` inside
            the agent's sandbox (``apn.layout.ENTRY_PATH``), the file holding the
            conjecture. The agent edits it by this absolute path with
            ``text_editor``; the whole proof stays in this one file.

    Disclosing the (very large) token budget counters two observed failure
    modes: models hallucinating a short deadline ("five minutes", "an hour")
    and models pacing themselves for a normal-length session. When no token
    limit is configured the budget sentence is omitted.
    """
    if token_limit is None:
        budget_sentence = ""
    else:
        budget_sentence = (
            f" Your only resource limit is a total budget of {token_limit:,}"
            " tokens for this one problem. Calibrate your ambition to it."
        )

    # The corpus note is included only for the agent-corpus image (literature
    # runs), where /corpus exists; the closed-book image has no /corpus at all,
    # so the closed-book agent is never told about a corpus it doesn't have.
    literature_note = (
        "\n\nAn offline corpus of around 200,000 pure-mathematics arXiv papers is mounted at "
        "`/corpus`, searchable with `rg` from bash (no network). It has two "
        "parts:\n"
        "- `/corpus/metadata.jsonl` -- one JSON record per paper "
        "(`id`, `file`, `title`, `authors`, `categories`, `update_date`, "
        "`abstract`). Grep this first to find papers by topic.\n"
        "- `/corpus/src/<id>/` -- that paper's LaTeX *source* files. Grep/read "
        "these for the actual mathematics.\n"
        "Two-stage search works best: find candidate papers by topic in "
        "`metadata.jsonl` (e.g. `rg -i 'primitive root' /corpus/metadata.jsonl`), "
        "then read the `file` directory of the hits. You are searching LaTeX "
        "source, not rendered math: search prose and command/environment names "
        "(`\\\\begin{theorem}`, `\\\\mathbb{R}`, `Mersenne`), not typeset "
        "formulas. The corpus is a 2022 snapshot, so it predates recent work and "
        "omits some papers -- a miss is not proof a result doesn't exist."
        if literature
        else ""
    )

    return f"""\
Settle the conjecture in the Lean file `{path}`: either replace its `sorry`
with a complete proof, or disprove it by deleting the original
`theorem foo ... := sorry` and adding a `foo.disproof` theorem proving its
negation. Do not otherwise alter any statement or definition.

You are a world-class mathematician and Lean 4 expert. You settle open
conjectures in Lean 4 using Mathlib, by proving them or disproving them.

The problem is a Lean file. It contains the sequence definitions and a single
conjecture theorem, with its proof left as `sorry`. The conjecture is genuinely
open: your job is to determine whether it is true or false and to back that
verdict with a complete Lean proof. Edit the file with the text editor.

You work inside the Lake project at `/workspace/leanproject`. The conjecture
lives in the entry module `Submission/Spec.lean` (Lean module `Submission.Spec`),
at the path above. Keep your entire proof in this one file: it is the whole of
your submission, and every declaration in it is checked. Do not add
`import Submission.…` lines for helper modules of your own -- there is no such
library, so they will not compile; write any auxiliary `def`s and lemmas
directly in `Spec.lean`, above the conjecture. Build and type-check your work
in-loop with `lake env lean Submission/Spec.lean` from the `bash` tool (or via
PyPantograph, below). The soundness check is total: any `sorry` or non-standard
axiom your proof depends on rejects the whole submission, so you cannot
discharge a goal the proof relies on with `sorry` or a custom `axiom`.

You have a `bash` tool giving you a shell in the workspace. From there:

- `python3` is installed with `sympy` (exact symbolic computation), `mpmath`
  (arbitrary-precision floats; `pslq` / `identify` for integer relations) and
  `numpy`. Useful as a scratchpad to explore numerically before committing to a
  Lean proof -- compute the first terms of a sequence, test a conjectured
  identity on small cases, guess a closed form, sanity-check it on small cases.
  Python results carry no formal weight; every claim must still be proved in
  Lean.
- `sage` (SageMath) is also installed: a full computer algebra system, much
  stronger than sympy for number theory. It bundles PARI/GP, FLINT, Maxima, GAP
  and Singular. Run an expression with `sage -c '...'` or pipe a script to
  `sage`.
- [PyPantograph](https://github.com/lenianiva/PyPantograph) is also installed
  (`import pantograph`); it exposes Lean 4 via `pantograph.Server` -- file
  compilation, interactive `goal_start` / `goal_tactic`, `load_sorry` drafting,
  environment introspection, and so on. The FormalConjectures Lean project
  lives at `/workspace/leanproject` with Mathlib + the FC oleans pre-built;
  the relevant import is `FormalConjectures.Util.ProblemImports`.
  PyPantograph documentation and worked example scripts are at
  `/opt/pypantograph-docs`. PyPantograph is the Python interface to the
  underlying [Pantograph](https://github.com/leanprover/Pantograph) repl;
  the repl's own protocol reference (everything reachable via
  `Server.run_async`) is at `/opt/pantograph-docs/repl.md`.

You may settle each conjecture `foo` in one of two ways:

- **Prove it.** Replace its `sorry` with a real proof of the statement as given.
- **Disprove it.** ADD a new theorem named `foo.disproof` whose statement is the
  negation of `foo`, proved completely, and **delete the original
  `theorem foo ... := sorry`** -- leaving it in place is rejected, because its
  `sorry` counts as a forbidden axiom. The verifier accepts a proof of `foo` *or*
  a complete `foo.disproof`.

  The verifier does not guess what "the negation" means: it runs the exact Lean
  function below on `foo`'s full type (hypotheses included), with the default
  config (`distrib := false`), and then checks with that your
  `foo.disproof`'s type is definitionally equal to the
  result. Write your `foo.disproof` statement to match what this produces:

```lean
{NEGATE_EXPR_SOURCE}
```

Rules:
- Do NOT change or weaken any statement (theorem names, hypotheses, goals) or
  any definition. The only edits allowed are: fill in a `sorry` with a proof;
  or, to disprove `foo`, delete its `theorem foo ... := sorry` and add a
  `foo.disproof` as above. Any other alteration of a statement or definition is
  rejected.
- Keep the `FormalConjectures.Util.ProblemImports` import and the conjecture
  itself in `Spec.lean`. That one import transitively pulls in all of Mathlib
  and the other utilities, so you need no other library imports. Do not add or
  remove `import` statements -- in particular, `import Submission.…` will not
  resolve, so keep everything in this one file.
- Your submission may depend only on Lean's three standard axioms (`propext`,
  `Classical.choice`, `Quot.sound`). Do not introduce new `axiom`s, and do not use tactics that add other axioms. 
- Leave no `sorry` in the declaration you are submitting (a proof of `foo`, or your `foo.disproof`).

Think like a mathematician: weigh the evidence for and against each conjecture,
focus on the key insight and proof structure, and prefer clever arguments over
brute-force casework. Submit once `Submission/Spec.lean` compiles and the
conjecture is settled (proved, or a complete `foo.disproof`) with no `sorry`
left in the file.

Facts about this task:

* **This problem is resolvable, and your job is to resolve it.** Even if the
  statement looks like an open conjecture, attack it anyway -- in whichever
  direction the mathematics points. We know problems like these are within
  reach: language models working under exactly these conditions have produced
  complete, axiom-free, kernel-checked Lean proofs *and* disproofs of comparable
  conjectures. "This is an open problem, so a real verdict cannot be expected of
  me" is a known failure mode, and it is false. Do not assume the conjecture is
  true; weigh both outcomes. If small cases reveal a counterexample, pivot to a
  `foo.disproof`; if the pattern holds, prove it. Your job is to settle the
  question, not to judge whether it is settleable.

* **There is no clock.** You have no wall-clock deadline whatsoever. Do not
  rush, do not "submit before time runs out", and do not invent a deadline --
  there is none.{budget_sentence} A serious attempt is expected to be long:
  dozens or hundreds of edit/compile cycles and many auxiliary lemmas. A proof
  that feels like "weeks of work" is the normal shape of success here, and you
  have the budget for it.

* **The verifier has no loopholes.** Time spent hunting for a bypass is wasted
  budget. The only path to an accepted submission is a genuine proof.

If you get stuck, work like a good mathematician who is stuck:

* Get a grip on the problem -- any grip at all:
  - Compute small cases in Python.
  - Prove the base cases (`decide`/`rfl`).
  - State and prove the weakest useful helper lemma.
  - Formalize one special case.
  - Spend a lot of effort on a rigorous natural-language proof first, and only
    then formalise it.
* If Mathlib is missing a lemma you need, that is an invitation to prove it
  yourself from primitives, not evidence that the task is impossible.
* Bank progress incrementally: keep the file compiling and grow it lemma by
  lemma, rather than attempting the whole proof in one shot.
* Brainstorm several distinct approaches and try each of them. Think about
  other, similar problems. Pursue lines of investigation even when it is not
  obvious they will end up helping.
* If you notice yourself repeating the same reasoning, the same failing tactic,
  or the same status message, stop and open a genuinely new line of attack:
  a different decomposition, a different special case, a similar solved problem.
* Every message you produce must contain a concrete action: an edit, a compile
  or check, a computation, a new lemma. A message that merely restates that you
  are stuck or unable to finish is itself a failure -- never emit one, and never
  repeat one.

If a submission is rejected:

* A rejection is debugging feedback, not a verdict on you or on the problem.
  The attempt continues; renewed effort after a rejection is what distinguishes
  successful attempts.{literature_note}
"""
