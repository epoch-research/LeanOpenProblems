# TODO / Known Bugs

## Known bugs

### 1. SafeVerify rejects valid proofs that reproduce a target's pattern-matching `def` (private-name / module-name mismatch)

**Severity:** high — silently scores correct submissions as incorrect (`I`).

**Symptom.** A submission that genuinely proves the target (compiles, sorry-free,
axiom-clean) is rejected by `safe_verify`. The recorded scorer explanation shows:

```
Found a problem ... with declaration _private._apn_score.target.0.a.match_1.eq_1: declaration not found in submission
Found a problem ... with declaration _private._apn_score.target.0.a.match_1.splitter: declaration not found in submission
Found a problem ... with declaration _private._apn_score.target.0.A258667_inner_sum: declaration not found in submission
...
```
(`metadata.stage == "safeverify"`.)

**Root cause.** `processFileDeclarations` (`apn/lean/safeverify/Main.lean:17`) collects
*every* declaration of kind `theorem`/`def`/`opaque`/`inductive`/`constructor` from
the target olean, with **no filtering of private or compiler-generated declarations**.
`checkTargets` (`apn/lean/safeverify/Main.lean:90`) then requires each target name to be
present in the submission under a **name-identical** lookup.

When the target spec defines a function by pattern matching (e.g. `def a (n : ℕ) := match n with ...`),
Lean auto-generates private equational lemmas (`a.match_1`, `a.match_1.eq_*`,
`.splitter`, `._arg_pusher`). Their mangled names embed the **module (file) name**:
- target compiled as `_apn_score/target.lean`     → `_private._apn_score.`**`target`**`.0.a.match_1.eq_1`
- submission compiled as `_apn_score/submission.lean` → `_private._apn_score.`**`submission`**`.0.a.match_1.eq_1`

These can never match across the two differently-named files, so SafeVerify reports
`declaration not found in submission` for every such lemma and rejects the sample.
The same mismatch cascades to the main `def` when it *references* a private helper:
`A258667` is reported as `definition type or value mismatch` because its body refers to
`A258667_inner_sum`, whose private name differs only in the module component. The agent
cannot avoid this: it may not rename/alter definitions, and the file name is fixed by
the scorer, not the agent.

**Trigger condition.** Any target spec whose definitions generate private
auto-generated declarations — a non-trivial `match` (multiple cases / nested patterns /
`termination_by` well-founded recursion), or explicit `private def`/`private lemma`
helpers in the spec. Specs with only theorems, or whose `def`s are simple enough not to
emit a separately-stored `match_1` (e.g. a 2-case structural recursion), are unaffected —
which is why most samples still score correctly.

**Reproduced E2E** in the scorer image (`…:LeanOpenProblems_scorer_0.1.2`) with the exact
`A028859` def (`match n with | 0 => 1 | 1 => 3 | (n+2) => 2*a(n+1)+2*a n; termination_by n`):
a submission that reproduces the def verbatim and proves its theorem (`by simp [a]`) is
rejected with `_private._apn_score.tg.0.a.match_1.eq_1: declaration not found` (and
`.eq_2/.eq_3/.splitter/._arg_pusher`) — the target module name `tg` baked into the name
cannot appear in the submission module `sg`.

**Blast radius** (run `oeis-38vs40-v1-1zgnbauzxorcnmhi`, 6 model runs, 233 samples,
149 rejected): **25 rejections carry this `_private … not found in submission`
signature, spanning 9 distinct problems** — i.e. ~1 in 6 of all rejections is (at
least partly) this bug, on problems whose spec defines a pattern-matching function.
Affected problem IDs:
`oeis_103311_conjecture_0`, `oeis_2897_conjecture_0`, `oeis_319303_conjecture_0`,
`oeis_339602_conjecture_1`, `oeis_340737_conjecture_0`, `oeis_A028859_conjecture_1`,
`oeis_A258667_conjecture_0`, `oeis_a103885_conjecture_0`, `oeis_a279612_conjecture_i`.
(`103311`, `A028859`, `A258667` are the cleanest: agents had complete, axiom-clean,
sorry-free proofs. For others the signature is in the final submission's verdict.)

**Possible fixes** (in vendored `apn/lean/safeverify/Main.lean`):
- Skip private / compiler-generated names when building `targetDecls` (e.g. via
  `Lean.isPrivateName` / `Name.isInternalDetail`). Auto-generated equational lemmas are
  an elaboration artifact — reproducing the `def` identically regenerates equivalents,
  so they need not be matched by name.
- Or: normalize/strip the `_private._apn_score.<file>.<idx>` prefix before comparison.
- Or: compile target and submission under the *same* module name so private mangling agrees.

### 2. SafeVerify peak memory is effectively unbounded on legitimate proofs (un-memoized `rebuildExpr`)

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

### 3. Disproof negation-matching accepts only one syntactic encoding of the negation

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
