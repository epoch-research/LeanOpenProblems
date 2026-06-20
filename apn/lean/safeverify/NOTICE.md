# Vendored SafeVerify (ported to Lean v4.29.1)

This directory vendors **SafeVerify** by GasStationManager
(<https://github.com/GasStationManager/SafeVerify>), the kernel-level proof
checker the paper uses for validation. It re-checks a submission against a target
specification using `Environment.replay` (à la `lean4checker`): it confirms each
target declaration is implemented with the same name, kind, and **kernel type**,
that definition bodies are unchanged (unless they were `sorry` stubs), and that
only the standard axioms (`propext`, `Quot.sound`, `Classical.choice`) are used —
so `sorryAx`, injected axioms, and statement tampering are all rejected.

Upstream targets Lean v4.27.0. Two kinds of change were made here.

**Version bumps** so it loads the v4.29.1 oleans our sandbox produces:

* `lean-toolchain`: `v4.27.0` -> `v4.29.1`
* `lakefile.lean`: dropped the `mathlib` build dependency (SafeVerify's own code
  imports only Lean core + `Cli`; Mathlib is supplied on `LEAN_PATH` at runtime),
  and bumped `Cli` to `v4.29.0`.

**One behavioural source change**, in `SafeVerify/Util.lean`: `negateExpr` — the
function `checkNegatedTheorem` applies to a target's type to validate a
`foo.disproof` submission — was reduced from a hand-written negation-normal-form
rewrite (pushing `¬` inwards: `¬ ∀ a, p a` to `∃ a, ¬ p a`, `∧` to `→`, the
`Ne`->`Eq` case, ...) to plain `¬ e` (`mkNot`), and the now-dead `NegateConfig`
was removed. The negation of a statement is `¬` of it by construction, so the
kernel `isDefEq` check no longer has to trust a bespoke syntactic transform (a
smaller trusted surface), and the agent submits `foo.disproof : ¬ (<statement
verbatim>)` rather than matching one exact NNF encoding (a `push_neg` in the
proof body recovers the old goal). `Main.lean` and the other `SafeVerify/*.lean`
files are unchanged from upstream.

See `LICENSE.txt` for the upstream license.
