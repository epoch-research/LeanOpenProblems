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
# Wagstaff primes

A Wagstaff prime is a prime number of the form $(2^p+1)/3$, where $p$ is an odd prime.
The first Wagstaff primes are $3$, $11$, $43$, $683$ and $2731$. It is not known whether
there are infinitely many Wagstaff primes.

*References:*
- [Wikipedia, Wagstaff prime](https://en.wikipedia.org/wiki/Wagstaff_prime)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [OEIS A000979](https://oeis.org/A000979)
-/

namespace WagstaffPrime

/-- A Wagstaff prime is a prime number of the form $(2^p+1)/3$, where $p$ is an odd prime. -/
def IsWagstaffPrime (q : ℕ) : Prop :=
  q.Prime ∧ ∃ p : ℕ, p.Prime ∧ Odd p ∧ q = (2 ^ p + 1) / 3

/-- Are there infinitely many Wagstaff primes, that is, primes of the form $(2^p+1)/3$ with
$p$ an odd prime? -/
theorem wagstaff_prime : {q : ℕ | IsWagstaffPrime q}.Infinite := by
  sorry

end WagstaffPrime

theorem WagstaffPrime.wagstaff_prime.disproof : ¬ (type_of% @WagstaffPrime.wagstaff_prime) := sorry
