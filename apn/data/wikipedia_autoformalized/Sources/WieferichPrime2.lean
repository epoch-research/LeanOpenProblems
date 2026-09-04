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
@[category research open, AMS 11]
theorem wieferich_prime_2 : answer(sorry) ↔ {p : ℕ | IsWieferichPrime p}.Infinite := by
  sorry

/-- The prime $1093$ is a Wieferich prime. -/
@[category test, AMS 11]
theorem isWieferichPrime_1093 : IsWieferichPrime 1093 := by
  refine ⟨by norm_num, ?_⟩
  decide +kernel

/-- The prime $3511$ is a Wieferich prime. -/
@[category test, AMS 11]
theorem isWieferichPrime_3511 : IsWieferichPrime 3511 := by
  refine ⟨by norm_num, ?_⟩
  decide +kernel

/-- The prime $2$ is not a Wieferich prime: $2^2 \nmid 2^1 - 1 = 1$. -/
@[category test, AMS 11]
theorem not_isWieferichPrime_two : ¬ IsWieferichPrime 2 := by
  norm_num [IsWieferichPrime]

/-- The prime $3$ is not a Wieferich prime: $3^2 \nmid 2^2 - 1 = 3$. -/
@[category test, AMS 11]
theorem not_isWieferichPrime_three : ¬ IsWieferichPrime 3 := by
  norm_num [IsWieferichPrime]

/-- The primality condition excludes $1$, which satisfies the divisibility condition alone. -/
@[category test, AMS 11]
theorem not_isWieferichPrime_one : ¬ IsWieferichPrime 1 := by
  norm_num [IsWieferichPrime]

end WieferichPrime2
