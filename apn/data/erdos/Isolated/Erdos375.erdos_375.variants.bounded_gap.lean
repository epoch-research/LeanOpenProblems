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
import FormalConjectures.Wikipedia.LegendreConjecture

/-!
# Erdős Problem 375

*References:*
 - [erdosproblems.com/375](https://www.erdosproblems.com/375)
 - [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
    theory. Monographies de L'Enseignement Mathematique (1980).
 - [RST75] Ramachandra, K. and Shorey, T. N. and Tijdeman, R., On Grimm's problem relating to
    factorisation of a block of consecutive integers. J. Reine Angew. Math. (1975), 109-124.
 -
-/

open Set Filter Topology Asymptotics

namespace Erdos375

/-- This is a proposition saying that for any `n ≥ 1` and any `k`, if `n + 1, ..., n + k` are all
composite, then there are distinct primes `p₁, ... pₖ` such that `pᵢ ∣ n + i` for all `1 ≤ i ≤ k`.
-/
def Erdos375Prop : Prop := ∀ n ≥ 1, ∀ k, (∀ i < k, ¬ (n + i + 1).Prime) →
    ∃ p : Fin k → ℕ, p.Injective ∧ ∀ i, (p i).Prime ∧ p i ∣ n + i + 1

/-- If `Erdos375Prop` is true, then `(n + 1).nth Prime - n.nth Prime < (n.nth Prime) ^ (1 / 2 - c)`
for some `c > 0`. -/
theorem erdos_375.variants.bounded_gap : Erdos375Prop →
    ∃ c > 0, ∀ᶠ n in atTop, (n + 1).nth Nat.Prime - n.nth Nat.Prime
    < (n.nth Nat.Prime : ℝ) ^ (1 / (2 : ℝ) - c) := by
  sorry

end Erdos375
