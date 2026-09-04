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
# Newman–Shanks–Williams primes

*References:*
 - [Wikipedia, Newman–Shanks–Williams prime](https://en.wikipedia.org/wiki/Newman%E2%80%93Shanks%E2%80%93Williams_prime)
 - [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
 - [A001333](https://oeis.org/A001333), [A088165](https://oeis.org/A088165),
   [A005850](https://oeis.org/A005850)
 - [NSW80] Newman, M., Shanks, D. and Williams, H. C., *Simple groups of square order and an
   interesting sequence of primes*. Acta Arithmetica 38 (1980), 129–140.

Let $S_0 = 1$, $S_1 = 1$ and $S_n = 2 S_{n-1} + S_{n-2}$ for $n \geq 2$, so that
$$S_n = \frac{(1 + \sqrt 2)^n + (1 - \sqrt 2)^n}{2}.$$
The first few terms are $1, 1, 3, 7, 17, 41, 99, \ldots$ ([A001333](https://oeis.org/A001333)).
Each term is half the corresponding companion Pell number.

A *Newman–Shanks–Williams prime* (NSW prime) is a prime number of the form $S_{2m+1}$, that is,
a prime term of odd index in this sequence. The first few NSW primes are
$7, 41, 239, 9369319, 63018038201, \ldots$ ([A088165](https://oeis.org/A088165)), with indices
$3, 5, 7, 19, 29, \ldots$ ([A005850](https://oeis.org/A005850)). The odd-index restriction
matters: $S_2 = 3$, $S_4 = 17$ and $S_8 = 577$ are prime but are not NSW primes.

The question asks whether there are infinitely many NSW primes.
-/

namespace NewmanShanksWilliamsPrime

/-- The sequence $S_n$ defined by $S_0 = 1$, $S_1 = 1$ and $S_{n+2} = 2 S_{n+1} + S_n$
([A001333](https://oeis.org/A001333)). Its terms of odd index are the candidates for
Newman–Shanks–Williams primes. -/
def nswSeq : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 1 + 1 => 2 * nswSeq (n + 1) + nswSeq n

/-- A natural number $p$ is a *Newman–Shanks–Williams prime* if it is prime and it is of the
form $S_{2m+1}$ for some $m$, where $S$ is the sequence `nswSeq`. Only odd indices are allowed:
for instance $S_2 = 3$ and $S_4 = 17$ are prime but are not NSW primes. -/
def IsNSWPrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ m : ℕ, p = nswSeq (2 * m + 1)

/--
Are there infinitely many Newman–Shanks–Williams primes? That is, are there infinitely many
primes of the form
$$S_{2m+1} = \frac{(1 + \sqrt 2)^{2m+1} + (1 - \sqrt 2)^{2m+1}}{2},$$
where $S_0 = S_1 = 1$ and $S_n = 2 S_{n-1} + S_{n-2}$ for $n \geq 2$?
-/
theorem newman_shanks_williams_prime :
    {p : ℕ | IsNSWPrime p}.Infinite := by
  sorry

end NewmanShanksWilliamsPrime

theorem NewmanShanksWilliamsPrime.newman_shanks_williams_prime.disproof : ¬ (type_of% @NewmanShanksWilliamsPrime.newman_shanks_williams_prime) := sorry
