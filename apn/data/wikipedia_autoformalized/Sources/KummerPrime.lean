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
# Kummer primes

A *Kummer number* (also called a Euclid number of the second kind) is an integer of the
form $p_n\# - 1$, where $p_n\# = p_1 p_2 \cdots p_n$ is the $n$-th primorial, the product
of the first $n$ primes. The first few Kummer numbers are
$1, 5, 29, 209, 2309, 30029, \ldots$ (OEIS A057588).

A *Kummer prime* is a Kummer number that is prime. It is not known whether there are
infinitely many Kummer primes.

*References:*
- [Wikipedia: Euclid number](https://en.wikipedia.org/wiki/Euclid_number)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [OEIS A057588](https://oeis.org/A057588)
-/

namespace KummerPrime

/--
The $n$-th Kummer number $p_n\# - 1$: the product of the first $n$ primes, minus one.

Here `Nat.nth Nat.Prime i` is the $(i+1)$-st prime (0-indexed), so the product over
`Finset.range n` is the product of the first $n$ primes. The degenerate values
`kummerNumber 0 = 0` and `kummerNumber 1 = 1` are not prime, so they do not affect the
conjecture below.
-/
noncomputable def kummerNumber (n : ℕ) : ℕ := (∏ i ∈ Finset.range n, i.nth Nat.Prime) - 1

@[category test, AMS 11]
theorem kummerNumber_zero : kummerNumber 0 = 0 := by
  simp [kummerNumber]

@[category test, AMS 11]
theorem kummerNumber_one : kummerNumber 1 = 1 := by
  simp [kummerNumber, Nat.nth_prime_zero_eq_two]

@[category test, AMS 11]
theorem kummerNumber_two : kummerNumber 2 = 5 := by
  simp [kummerNumber, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three]

@[category test, AMS 11]
theorem kummerNumber_three : kummerNumber 3 = 29 := by
  simp [kummerNumber, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]

/-- $7\# - 1 = 209 = 11 \cdot 19$ is the first composite Kummer number. -/
@[category test, AMS 11]
theorem kummerNumber_four : kummerNumber 4 = 209 := by
  simp [kummerNumber, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]

/-- The Kummer number $5\# - 1 = 29$ is prime. -/
@[category test, AMS 11]
theorem kummerNumber_three_prime : (kummerNumber 3).Prime := by
  rw [kummerNumber_three]
  norm_num

/-- The Kummer number $7\# - 1 = 209$ is not prime. -/
@[category test, AMS 11]
theorem kummerNumber_four_not_prime : ¬ (kummerNumber 4).Prime := by
  rw [kummerNumber_four]
  norm_num

/--
**Kummer primes.** Are there infinitely many Kummer primes? That is, are there infinitely
many $n$ such that the Kummer number $p_n\# - 1$ is prime?

Since $n \mapsto p_n\# - 1$ is strictly increasing for $n \ge 1$, this is equivalent to
asking whether infinitely many primes are of the form $p_n\# - 1$.
-/
@[category research open, AMS 11]
theorem kummer_prime : answer(sorry) ↔ {n | (kummerNumber n).Prime}.Infinite := by
  sorry

end KummerPrime
