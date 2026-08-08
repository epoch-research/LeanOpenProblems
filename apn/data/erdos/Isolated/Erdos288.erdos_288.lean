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
Is it true that there are only finitely many pairs of intervals $I_1$, $I_2$ such that
$$
\sum_{n_1 \in I_1} \frac{1}{n_1} + \sum_{n_2 \in I_2} \frac{1}{n_2} \in \mathbb{N}?
$$
-/
theorem erdos_288 : Set.Finite { I : Fin 2 → ℕ+ × ℕ+ |
    ∀ j, (I j).1 ≤ (I j).2 ∧
      ∃ n : ℕ+, (∑ j : Fin 2, ∑ nⱼ ∈ Set.Icc (I j).1 (I j).2, (nⱼ⁻¹ : ℚ)) = n } := by
  sorry

end Erdos288
