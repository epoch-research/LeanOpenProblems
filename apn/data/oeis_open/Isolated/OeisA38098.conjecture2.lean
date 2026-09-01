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
# Number of primes $< n^3$

Number of primes strictly less than $n^3$.

*References:*
- [A038098](https://oeis.org/A038098)-/

namespace OeisA38098

/-- Number of primes strictly less than $n^3$. -/
def a (n : ℕ) : ℕ := (Nat.primesBelow (n ^ 3)).card

/--
Conjecture (ii): all the numbers $\pi(n^2)/n^2$ ($n = 1, 2, 3, \ldots$) are pairwise distinct.
Moreover, we have $\pi(n^2)/n^2 > \pi((n+1)^2)/(n+1)^2$ for all $n > 15646$.
- Zhi-Wei Sun, Oct 17 2015
-/
theorem conjecture2 :
    (∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      (Nat.primeCounting (m ^ 2) : ℚ) / (m ^ 2 : ℚ) =
      (Nat.primeCounting (n ^ 2) : ℚ) / (n ^ 2 : ℚ) → m = n) ∧
    (∀ n : ℕ, 15646 < n →
      (Nat.primeCounting ((n + 1) ^ 2) : ℚ) / ((n + 1) ^ 2 : ℚ) <
      (Nat.primeCounting (n ^ 2) : ℚ) / (n ^ 2 : ℚ)) := by
  sorry

end OeisA38098

theorem OeisA38098.conjecture2.disproof : ¬ (type_of% @OeisA38098.conjecture2) := sorry
