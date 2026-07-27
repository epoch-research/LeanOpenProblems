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
# Erdős Problem 951

*References:*
 - [erdosproblems.com/951](https://www.erdosproblems.com/951)
 - [Er77c] Erdős, Paul, Problems and results on combinatorial number theory. III. Number theory day (Proc. Conf., Rockefeller Univ.,
    New York, 1976) (1977), 43-72.
-/

open scoped Finsupp Nat.Prime Topology
open Filter

namespace Erdos951

/-- A sequence `a : ℕ → ℝ` is said to have property `Erdos951Prop` if for any pair of distinct
finitely supported sequences `k l : ℕ →₀ ℕ` their corresponding Beurling integers are of distance
at least one apart. -/
def Erdos951Prop (a : ℕ → ℝ) : Prop :=
  ∀ (k ℓ : ℕ →₀ ℕ), k ≠ ℓ → |beurlingInteger a k - beurlingInteger a ℓ| ≥ 1

/-- If `1 < a 0 < ...` has property `Erdos951Prop`, is it true that `#{a i ≤ x} ≤ π x`? -/
@[category research open, AMS 11]
theorem erdos_951 : 
    ∀ a : ℕ → ℝ, 1 < a 0 → StrictMono a → Erdos951Prop a →
      ∀ᶠ (x : ℝ) in Filter.atTop, {i : ℕ | a i ≤ x}.ncard ≤ π ⌊x⌋₊ := by
  sorry

end Erdos951
