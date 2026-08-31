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
Is it true for any $k > 2$ that only finitely many $k$ intervals satisfy this condition?
-/
theorem erdos_288.variants.exists_k_gt_2 : 
    ∃ k > 2, Set.Finite { I : Fin k → ℕ+ × ℕ+ |
      ∀ j, (I j).1 ≤ (I j).2 ∧
        ∃ n : ℕ+, (∑ j : Fin k, ∑ nⱼ ∈ Set.Icc (I j).1 (I j).2, (nⱼ⁻¹ : ℚ)) = n } := by
  sorry

end Erdos288

theorem Erdos288.erdos_288.variants.exists_k_gt_2.disproof : ¬ (type_of% @Erdos288.erdos_288.variants.exists_k_gt_2) := sorry
