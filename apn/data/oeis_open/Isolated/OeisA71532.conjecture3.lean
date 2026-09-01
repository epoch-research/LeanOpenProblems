/-
Copyright 2026 The Formal Conjectures Authors.

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

import FormalConjecturesUtil

/-!
# Alternating sum of signs of powers of $3/2$

The sequence $a(n) = -\sum_{k=1}^n (-1)^{\lfloor (3/2)^k \rfloor}$.

*References:*
- [A071532](https://oeis.org/A071532)-/

namespace OeisA71532

open Finset Filter
open scoped Asymptotics

/-- The sequence $a(n) = -\sum_{k=1}^n (-1)^{\lfloor (3/2)^k \rfloor}$. -/
def a (n : ℕ) : ℤ :=
  - ∑ k ∈ Icc 1 n, (-1 : ℤ) ^ (3 ^ k / 2 ^ k)

/--
Conjecture: asymptotically, $a(n) \sim C \log(n)^2$ for some constant $C > 0$.
-/
theorem conjecture3 :
    ∃ C : ℝ, 0 < C ∧ (fun n : ℕ ↦ (a n : ℝ)) ~[atTop] (fun n : ℕ ↦ C * Real.log (n : ℝ) ^ 2) := by
  sorry

end OeisA71532

theorem OeisA71532.conjecture3.disproof : ¬ (type_of% @OeisA71532.conjecture3) := sorry
