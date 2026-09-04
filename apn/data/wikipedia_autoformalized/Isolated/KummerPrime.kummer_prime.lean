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

/--
**Kummer primes.** Are there infinitely many Kummer primes? That is, are there infinitely
many $n$ such that the Kummer number $p_n\# - 1$ is prime?

Since $n \mapsto p_n\# - 1$ is strictly increasing for $n \ge 1$, this is equivalent to
asking whether infinitely many primes are of the form $p_n\# - 1$.
-/
theorem kummer_prime : {n | (kummerNumber n).Prime}.Infinite := by
  sorry

end KummerPrime

theorem KummerPrime.kummer_prime.disproof : ¬ (type_of% @KummerPrime.kummer_prime) := sorry
