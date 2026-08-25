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
# Erdős Problem 359

*Reference:* [erdosproblems.com/359](https://www.erdosproblems.com/359)
-/

namespace Erdos359

open Filter Asymptotics

/-- The predicate that `A` is monotone, `A 0 = n` and for all `j`, `A (j + 1)` is the smallest natural number that
cannot be written as a sum of consecutive terms of `A 0, ..., A j` -/
def IsGoodFor (A : ℕ → ℕ) (n : ℕ) : Prop := A 0 = n ∧ StrictMono A ∧
  ∀ j, IsLeast
    {m : ℕ | A j < m ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → m ≠ ∑ i ∈ Finset.Icc a b, A i}
    (A <| j + 1)

/-- Suppose monotone sequence $A$ satisfies the following: `A 0 = 1` and for all `j`, `A (j + 1)` is the
smallest natural number that cannot be written as a sum of consecutive terms of `A 0, ..., A j`.
Then it is conjectured that $$a_k ~ \frac{k \log k}{\log \log k}$$. -/
theorem erdos_359.variants.isGoodFor_1_asymptotic (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    (fun k ↦ (A k : ℝ)) ~[atTop] (fun k ↦ k * (k : ℝ).log / (k : ℝ).log.log) := by
  sorry

end Erdos359

theorem Erdos359.erdos_359.variants.isGoodFor_1_asymptotic.disproof : ¬ (type_of% @Erdos359.erdos_359.variants.isGoodFor_1_asymptotic) := sorry
