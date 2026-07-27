/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 931

*Reference:* [erdosproblems.com/931](https://www.erdosproblems.com/931)
-/

namespace Erdos931

/--
Erdős thought perhaps if the two products have the same factors then
$n_2 > 2(n_1 + k_1)$.
It is an open question whether this is true when allowing a finite number of counterexamples.
-/
@[category research open, AMS 11]
theorem erdos_931.variants.additional_condition : ∀ᵉ (k₁ : ℕ) (k₂ ≥ 3), k₂ ≤ k₁ →
    {(n₁, n₂) | n₁ + k₁ ≤ n₂ ∧ n₂ ≤ 2 * (n₁ + k₁) ∧
      (∏ i ∈ Finset.Icc 1 k₁, (n₁ + i)).primeFactors =
      (∏ j ∈ Finset.Icc 1 k₂, (n₂ + j)).primeFactors}.Finite := by
  sorry

end Erdos931
