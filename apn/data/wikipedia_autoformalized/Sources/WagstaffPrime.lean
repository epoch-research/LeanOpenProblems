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

/-- For odd $p$, the number $2^p+1$ is divisible by $3$, so $(2^p+1)/3$ is an exact quotient. -/
@[category API, AMS 11]
theorem three_dvd_two_pow_add_one {p : ℕ} (hp : Odd p) : 3 ∣ 2 ^ p + 1 := by
  simpa using hp.nat_add_dvd_pow_add_pow 2 1

/-- The prime $3 = (2^3+1)/3$ is a Wagstaff prime. -/
@[category test, AMS 11]
theorem isWagstaffPrime_three : IsWagstaffPrime 3 :=
  ⟨by norm_num, 3, by norm_num, by decide, by norm_num⟩

/-- The prime $11 = (2^5+1)/3$ is a Wagstaff prime. -/
@[category test, AMS 11]
theorem isWagstaffPrime_eleven : IsWagstaffPrime 11 :=
  ⟨by norm_num, 5, by norm_num, by decide, by norm_num⟩

/-- The prime $43 = (2^7+1)/3$ is a Wagstaff prime. -/
@[category test, AMS 11]
theorem isWagstaffPrime_fortyThree : IsWagstaffPrime 43 :=
  ⟨by norm_num, 7, by norm_num, by decide, by norm_num⟩

/-- The number $1 = (2^1+1)/3$ is not a Wagstaff prime: it is not prime and $1$ is not a prime
exponent. -/
@[category test, AMS 11]
theorem not_isWagstaffPrime_one : ¬ IsWagstaffPrime 1 := by
  norm_num [IsWagstaffPrime]

/-- The prime $5$ is not of the form $(2^p+1)/3$ with $p$ an odd prime, so $5$ is not a
Wagstaff prime. -/
@[category test, AMS 11]
theorem not_isWagstaffPrime_five : ¬ IsWagstaffPrime 5 := by
  rintro ⟨-, p, hp, hodd, h⟩
  have hlt : p < 5 := by
    by_contra! hle
    have : 2 ^ 5 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hle
    omega
  interval_cases p <;> first | omega | norm_num at hp

/-- Are there infinitely many Wagstaff primes, that is, primes of the form $(2^p+1)/3$ with
$p$ an odd prime? -/
@[category research open, AMS 11]
theorem wagstaff_prime : answer(sorry) ↔ {q : ℕ | IsWagstaffPrime q}.Infinite := by
  sorry

end WagstaffPrime
