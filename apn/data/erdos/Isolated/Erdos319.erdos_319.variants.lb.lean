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
# Erdős Problem 319

*Reference:* [erdosproblems.com/319](https://www.erdosproblems.com/319)
-/

open Filter

open scoped Topology Finset Real

namespace Erdos319

/-- Adenwalla has observed that a lower bound (on the maximum size of $A$) of
$$
  |A| \geq (1 - \frac{1}{e} + o(1))N
$$
follows from the main result of Croot [Cr01].

[Cr01] Croot, III, Ernest S., _On unit fractions with denominators in short intervals_.
Acta Arith. (2001), 99-114.
-/
theorem erdos_319.variants.lb : ∃ (o : ℕ → ℝ), (o =o[atTop] (1 : ℕ → ℝ)) ∧
    ∀ᶠ N in atTop, (1 - 1 / rexp 1 + o N) * N ≤ sSup { (#A : ℝ) | (A) (_ : A ⊆ Finset.Icc 1 N)
      (_ : ∃ δ : ℕ → ℤˣ, ∑ n ∈ A, (δ n : ℚ) / n = 0 ∧
        ∀ A' ⊂ A, A'.Nonempty → ∑ n ∈ A', (δ n : ℚ) / n ≠ 0) } := by
  sorry

end Erdos319
