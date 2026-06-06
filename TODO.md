# TODO / Known Bugs

## Known bugs

### 1. SafeVerify peak memory is effectively unbounded on legitimate proofs (un-memoized `rebuildExpr`)

**Severity:** medium — causes deterministic scorer OOM kills (infra errors / lost samples),
not mis-scoring. Already documented in code; tracked here for visibility.

**Detail** (see `apn/task.py:96-121` and `apn/checker.py:36-44`):
- `safe_verify` has a large fixed footprint (~27 GiB peak RSS), attributed almost
  entirely to four `importModules` calls (two in the import-superset check, one per
  replayed file), each materializing the full Mathlib environment and never freeing it.
- On top of that, proof *content* is unbounded: `rebuildExpr` deep-copies proof terms
  **without memoization**, expanding pointer-shared DAGs (which tactics like `ring`
  produce routinely) into trees. Measured: `(a+b+c)^16 = (c+b+a)^16 := by ring` compiles
  agent-side in 3.5s at 6.4 GiB but blew past a 34 GiB limit in safe_verify before being
  OOM-killed. Real submissions have reached ~43 GiB in production. `mem_limit` is set to
  `50g` to cover the worst observation, but no limit can make scorer OOMs impossible.
- Agent-side compile success does **not** bound the scorer's cost.

**Possible fixes** (in vendored `safeverify`):
- Memoize `rebuildExpr` so shared sub-terms are copied once.
- Skip the redundant `importModules` in the import-superset check.

### 2. Disproof negation-matching accepts only one syntactic encoding of the negation

**Severity:** medium — the verifier accepts a disproof only if it is written in `negateExpr`'s
exact shape, rejecting the encoding a mathematician would write first. The prompt works around
this by handing the agent the literal `negateExpr`; the matcher strictness itself remains.

**Mechanism.** `checkNegatedTheorem` (`apn/lean/safeverify/SafeVerify/Util.lean:128`) accepts a
`foo.disproof` iff `Kernel.isDefEq(negateExpr(targetType), submissionType)`. `negateExpr`
(`Util.lean:101`) turns **every** `forallE` — including a hypothesis binder `(h : 0 < n)` or an
implication `H → R`, which is `∀ (_ : H), R` — into a nested `Exists` over the proof:

- target `∀ n, 0 < n → P n`  →  `negateExpr`  →  `∃ n, ∃ (_ : 0 < n), ¬ P n`

The idiomatic disproof instead carries hypotheses with `∧`: `∃ n, 0 < n ∧ ¬ P n`. But
`@Exists (0 < n) (fun _ => ¬ P n)` and `@And (0 < n) (¬ P n)` are different inductive
type-formers and are **not** `isDefEq`, and `isDefEq` is the only matcher (no
propositional-equivalence fallback). So the `∧` form never matches; the agent must reproduce
`negateExpr`'s exact nested-`∃` encoding. (Hypothesis-free `∀ x, P x` → `∃ x, ¬ P x` matches
fine; the strictness bites only on carried hypotheses.)

**Fix — make the matcher accept either encoding** (verifier change):
- Also build the `∧`/idiomatic form and try `isDefEq` against both; or compare modulo
  `Exists`-of-`Prop` ⟷ `And`; or check propositional inter-derivability rather than raw
  `isDefEq`.
- Or have `negateExpr` emit `And` for proof-irrelevant (`Prop`-typed) binders, so its output
  is the `∃ x, hyp ∧ ¬goal` form.

Add a unit test over representative target shapes (∀+hyp, ∀+→, ∧ goal, ∨ goal, ≠, plain).

The agent prompt (`apn/prompts.py`) already embeds the literal `negateExpr` and states that the
verifier applies it, so honest disproofs can be written to match today. This fix would let the
natural `∃ x, hyp ∧ ¬goal` form pass too.

**E2E evidence** (scorer image, target `theorem foo (n : ℕ) (h : 0 < n) : n = n + 1`). Both
submissions delete the original `foo` and submit only a `foo.disproof`, so the sole variable
is the negation encoding:

| `foo.disproof` statement | `safe_verify --disproofs` |
|---|---|
| `∃ n, 0 < n ∧ n ≠ n + 1` (idiomatic `∧`) | REJECT (exit 1) — `foo: theorem type mismatch` |
| `∃ n, ∃ _ : 0 < n, n ≠ n + 1` (`negateExpr` form) | PASS (exit 0) |

Only the `negateExpr` encoding is accepted.
