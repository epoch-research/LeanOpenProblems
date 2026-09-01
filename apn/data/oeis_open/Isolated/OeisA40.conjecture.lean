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
# The prime numbers

The $n$-th prime number $p_n$, where $p_1 = 2$.

*References:*
- [A000040](https://oeis.org/A000040)
-/

namespace OeisA40

/-- The sequence of prime numbers, with $a(0) = 0$ and $a(n) = p_n$ for $n \ge 1$. -/
noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n' + 1 => Nat.nth Nat.Prime n'

/--
**Conjecture from Thomas Ordowski (2023)**:
$\log \log a(n+1) - \log \log a(n) < 1/n$ for $n > 0$.
-/
theorem conjecture (n : ℕ) (hn : 0 < n) :
    Real.log (Real.log (a (n + 1) : ℝ)) - Real.log (Real.log (a n : ℝ)) < 1 / (n : ℝ) := by
  sorry

end OeisA40

theorem OeisA40.conjecture.disproof : ¬ (type_of% @OeisA40.conjecture) := sorry
