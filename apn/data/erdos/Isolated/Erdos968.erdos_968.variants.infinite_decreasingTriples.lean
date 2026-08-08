/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 968

Let `uₙ = pₙ / n`, where `pₙ` is the `n`th prime. Does the set of `n` such that `uₙ < uₙ₊₁`
have positive density?

Erdős and Prachar also proved that `∑_{pₙ < x} |uₙ₊₁ - uₙ| ≍ (log x)^2`, and that the set of `n`
such that `uₙ > uₙ₊₁` has positive density. Erdős also asked whether there are infinitely many
increasing triples `uₙ < uₙ₊₁ < uₙ₊₂` or decreasing triples `uₙ > uₙ₊₁ > uₙ₊₂`.

*Reference:* [erdosproblems.com/968](https://www.erdosproblems.com/968)

[ErPr61] Erdős, P. and Prachar, K., _Sätze und Probleme über pₖ/k_. Abh. Math. Sem. Univ. Hamburg
(1961/62), 251–256.
-/

open Filter Real
open scoped BigOperators

namespace Erdos968

/--
`u n` is the normalized `n`th prime, defined as `pₙ / (n+1)` where `pₙ` is the `n`th prime
(with `0.nth Nat.Prime = 2`).

This corresponds to the classical sequence `(p₁/1, p₂/2, p₃/3, ...)` while using `Nat.nth Prime`'s
`0`-based indexing; in particular, the denominator is always positive.
-/
noncomputable def u (n : ℕ) : ℝ :=
  (n.nth Nat.Prime : ℝ) / (n + 1)

/--
Erdős asked whether there are infinitely many solutions to `uₙ > uₙ₊₁ > uₙ₊₂`.
-/
theorem erdos_968.variants.infinite_decreasingTriples :
    {n : ℕ | u n > u (n + 1) ∧ u (n + 1) > u (n + 2)}.Infinite := by
  sorry

end Erdos968
