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
# Erdős Problem 288

*Reference:* [erdosproblems.com/288](https://www.erdosproblems.com/288)
-/

namespace Erdos288

/--
This is still open even if $|I_2| = 1$.
-/
theorem erdos_288.variants.i2_card_eq_1 : Set.Finite { (I, n₂) : (ℕ+ × ℕ+) × ℕ+ |
    I.1 ≤ I.2 ∧ ∃ n : ℕ+, ∑ n₁ ∈ Set.Icc I.1 I.2, (n₁⁻¹ : ℚ) + (n₂⁻¹ : ℚ) = n } := by
  sorry

end Erdos288

theorem Erdos288.erdos_288.variants.i2_card_eq_1.disproof : ¬ (type_of% @Erdos288.erdos_288.variants.i2_card_eq_1) := sorry
