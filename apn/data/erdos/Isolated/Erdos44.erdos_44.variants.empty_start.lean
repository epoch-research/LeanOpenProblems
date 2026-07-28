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
# Erdős Problem 44: Extending Sidon Sets

*Reference:* [erdosproblems.com/44](https://www.erdosproblems.com/44)
-/

open Function Set Finset

namespace Erdos44

/--
The case where we start with an empty set (constructing large Sidon sets).
-/
theorem erdos_44.variants.empty_start : ∀ᵉ (ε > (0 : ℝ)), ∀ᶠ (M : ℕ) in Filter.atTop,
    ∃ᵉ (A ⊆ Finset.Icc 1 M), IsSidon (A : Set ℕ) ∧ (1 - ε) * Real.sqrt M ≤ A.card := by
  sorry

/-  ## Related results and examples -/

end Erdos44
