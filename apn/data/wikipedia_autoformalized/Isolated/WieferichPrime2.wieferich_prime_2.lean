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
# Wieferich primes

A Wieferich prime is a prime $p$ such that $p^2$ divides $2^{p-1} - 1$. The only known
examples are $1093$ and $3511$. It is an open question whether there are infinitely many
Wieferich primes; the conjectured answer is affirmative.

*References:*
* [Wikipedia, Wieferich prime](https://en.wikipedia.org/wiki/Wieferich_prime)
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [OEIS A001220](https://oeis.org/A001220)
-/

namespace WieferichPrime2

/-- A Wieferich prime is a prime $p$ such that $p^2 \mid 2^{p-1} - 1$. -/
def IsWieferichPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ^ 2 ∣ 2 ^ (p - 1) - 1

/-- Are there infinitely many Wieferich primes, i.e. primes $p$ with $p^2 \mid 2^{p-1} - 1$?
The conjectured answer is affirmative. -/
theorem wieferich_prime_2 : {p : ℕ | IsWieferichPrime p}.Infinite := by
  sorry

end WieferichPrime2

theorem WieferichPrime2.wieferich_prime_2.disproof : ¬ (type_of% @WieferichPrime2.wieferich_prime_2) := sorry
