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
# Practical numbers

A positive integer $n$ is called a *practical number* (or *panarithmic number*) if every positive
integer $m \le n$ can be represented as a sum of distinct divisors of $n$.

*References:*
- [A005153](https://oeis.org/A005153)
-/

namespace OeisA5153

/-- A positive integer $n$ is practical if every $m \le n$ can be represented as a sum of
distinct divisors of $n$. -/
def A (n : ℕ) : Prop :=
  0 < n ∧ Nat.IsPractical n

/--
Conjecture: every odd number, beginning with 3, is the sum of a prime number and a practical
number.
- Hal M. Switkay, Jan 28 2023
-/
theorem conjecture (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    ∃ p q : ℕ, p.Prime ∧ A q ∧ n = p + q := by
  sorry

end OeisA5153

theorem OeisA5153.conjecture.disproof : ¬ (type_of% @OeisA5153.conjecture) := sorry
