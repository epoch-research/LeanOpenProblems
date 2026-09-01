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
# Sum of next $n$ primes

The sum of the primes in the $n$-th row of the prime number triangle:
$$a(n) = \sum_{i = 1 + n(n-1)/2}^{n + n(n-1)/2} p_i$$
with $a(0) = 0$.

*References:*
- [A007468](https://oeis.org/A007468)
-/

namespace OeisA7468

/-- Sum of the next $n$ primes, with $a(0) = 0$. -/
noncomputable def a (n : ℕ) : ℕ :=
  let startIdx : ℕ := (n * (n - 1)) / 2
  ∑ i ∈ Finset.range n, Nat.nth Nat.Prime (startIdx + i)

/--
The only positive integer $n$ such that $a(n)$ is a perfect square is $n=38$.
- Carlos Eduardo Olivieri, Mar 09 2015
-/
theorem conjecture (n : ℕ) (hn : 0 < n) (hsq : IsSquare (a n)) : n = 38 := by
  sorry

end OeisA7468

theorem OeisA7468.conjecture.disproof : ¬ (type_of% @OeisA7468.conjecture) := sorry
