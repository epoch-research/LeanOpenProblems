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
# Erdős Problem 868

*References:*
- [erdosproblems.com/868](https://www.erdosproblems.com/868)
-/

open Filter

open scoped Pointwise

namespace Erdos868

/-- The number of ways in which a natural `n` can be written as the sum of
`o` members of the set `A`. -/
noncomputable
def ncard_add_repr (A : Set ℕ) (o : ℕ) (n : ℕ) : ℕ :=
  { a : Fin o → ℕ | Set.range a ⊆ A ∧ ∑ i, a i = n }.ncard

/-- Let $A$ be an additive basis of order $2$, let $f(n)$ denote the number of ways in which
$n$ can be written as the sum of two elements from $A$. If $f(n) \to \infty$ as $n \to \infty$, then
must $A$ contain a minimal additive basis of order $2$?
-/
theorem erdos_868.parts.i :
    ∀ (A : Set ℕ), A.IsAsymptoticAddBasisOfOrder 2 →
      atTop.Tendsto (fun n => ncard_add_repr A 2 n) atTop → ∃ B ⊆ A,
      B.IsAsymptoticAddBasisOfOrder 2 ∧ ∀ b ∈ B, ¬(B \ {b}).IsAsymptoticAddBasisOfOrder 2 := by
  sorry

end Erdos868
