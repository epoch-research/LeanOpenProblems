# Vendored SafeVerify (ported to Lean v4.29.1)

This directory vendors **SafeVerify** by GasStationManager
(<https://github.com/GasStationManager/SafeVerify>), the kernel-level proof
checker the paper uses for validation. It re-checks a submission against a target
specification using `Environment.replay` (à la `lean4checker`): it confirms each
target declaration is implemented with the same name, kind, and **kernel type**,
that definition bodies are unchanged (unless they were `sorry` stubs), and that
only the standard axioms (`propext`, `Quot.sound`, `Classical.choice`) are used —
so `sorryAx`, injected axioms, and statement tampering are all rejected.

Upstream targets Lean v4.27.0. The **only** changes made here are version bumps
so it loads the v4.29.1 oleans our sandbox produces:

* `lean-toolchain`: `v4.27.0` -> `v4.29.1`
* `lakefile.lean`: dropped the `mathlib` build dependency (SafeVerify's own code
  imports only Lean core + `Cli`; Mathlib is supplied on `LEAN_PATH` at runtime),
  and bumped `Cli` to `v4.29.0`.

No `Main.lean` / `SafeVerify/*.lean` source changes were required. See
`LICENSE.txt` for the upstream license.
