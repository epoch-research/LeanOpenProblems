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
# Erdős Problem 392

*Reference:* [erdosproblems.com/392](https://www.erdosproblems.com/392)
-/

open Filter

open scoped Nat

namespace Erdos392

/--
Cambie has observed that a positive answer follows from the result above with $a_t \leq n$, simply
by pairing variables together, e.g. taking $a'_i = a_{2i-1}a_{2i}$ (and the lower bound follows from
Stirling's approximation).
-/
theorem erdos_392.variants.implication (h : ∀ (A : ℕ → ℕ) (h : ∀ n > 0, IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧ Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)), ((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n)) :
    ∀ (A : ℕ → ℕ) (hA : ∀ n > 0, IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧ Monotone a ∧ a (Fin.last t) ≤ n) } (A n)), (fun (n : ℕ) => (A n - n + n / Real.log n : ℝ)) =o[atTop] fun n => n / Real.log n := by
  sorry

end Erdos392
