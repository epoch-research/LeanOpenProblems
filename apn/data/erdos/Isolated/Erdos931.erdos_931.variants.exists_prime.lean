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
Erdős was unable to prove that if the two products have the same factors
then there must exist a prime between $n_1$ and $n_2$.
-/
theorem erdos_931.variants.exists_prime (k₁ k₂ n₁ n₂ : ℕ) (h₁ : k₂ ≤ k₁) (h₂ : 3 ≤ k₂)
    (h₃ : n₁ + k₁ ≤ n₂) (h₄ : (∏ i ∈ Finset.Icc 1 k₁, (n₁ + i)).primeFactors =
      (∏ j ∈ Finset.Icc 1 k₂, (n₂ + j)).primeFactors) :
    ∃ (p : ℕ), p.Prime ∧ n₁ ≤ p ∧ p ≤ n₂ := by
  sorry

end Erdos931

theorem Erdos931.erdos_931.variants.exists_prime.disproof : ¬ (type_of% @Erdos931.erdos_931.variants.exists_prime) := sorry
