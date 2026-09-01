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
# Wilson primes

A Wilson prime is a prime $p$ for which $p^2$ divides $(p-1)!+1$. The only known examples are
$5$, $13$, and $563$. It is conjectured that infinitely many Wilson primes exist.

*References:*
* [Wikipedia, Wilson prime](https://en.wikipedia.org/wiki/Wilson_prime)
* [OEIS A007540](https://oeis.org/A007540)
* E. Costa, R. Gerbicz, and D. Harvey,
  [A search for Wilson primes](https://arxiv.org/abs/1209.3436)
-/

namespace WilsonPrime

/-- A Wilson prime is a prime $p$ such that $p^2 \mid (p-1)!+1$. -/
def IsWilsonPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ^ 2 ∣ (p - 1).factorial + 1

/-- There are infinitely many Wilson primes. -/
theorem infinitely_many_wilson_primes : Set.Infinite {p : ℕ | IsWilsonPrime p} := by
  sorry

end WilsonPrime

theorem WilsonPrime.infinitely_many_wilson_primes.disproof : ¬ (type_of% @WilsonPrime.infinitely_many_wilson_primes) := sorry
