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
# Wieferich primes in base 47

A *Wieferich prime in base $a$* is a prime $p$ such that $a^{p-1} \equiv 1 \pmod{p^2}$.
The classical Wieferich primes are those in base $2$; the only known ones are $1093$ and $3511$.
Base $47$ is the smallest base $a > 1$ for which no Wieferich prime is known.

*References:*
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [Wikipedia, Wieferich prime](https://en.wikipedia.org/wiki/Wieferich_prime)
* [OEIS A039951](https://oeis.org/A039951)
-/

namespace WieferichPrime

/--
Are there any Wieferich primes in base $47$? That is, does there exist a prime $p$ such that
$p^2 \mid 47^{p-1} - 1$?

The usual proviso $p \nmid 47$ is omitted because it is automatic: the prime $p = 47$ does not
satisfy the divisibility condition.
-/
@[category research open, AMS 11]
theorem wieferich_prime : answer(sorry) ↔ ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ 47 ^ (p - 1) - 1 := by
  sorry

/-- The prime $47$ is not a Wieferich prime in base $47$, so no coprimality hypothesis is needed
in `wieferich_prime`. -/
@[category test, AMS 11]
theorem not_dvd_of_eq_47 : ¬ 47 ^ 2 ∣ 47 ^ (47 - 1) - 1 := by
  norm_num

/-- The prime $2$ is not a Wieferich prime in base $47$: $47^1 - 1 = 46$ is not divisible by
$4$. -/
@[category test, AMS 11]
theorem not_dvd_of_eq_two : ¬ 2 ^ 2 ∣ 47 ^ (2 - 1) - 1 := by
  norm_num

end WieferichPrime
