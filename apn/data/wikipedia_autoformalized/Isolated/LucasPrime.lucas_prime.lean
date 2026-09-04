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
# Lucas primes

The Lucas numbers are defined by $L_0 = 2$, $L_1 = 1$ and $L_{n+2} = L_{n+1} + L_n$.
A Lucas prime is a Lucas number that is prime. The first few Lucas primes are
$2, 3, 7, 11, 29, 47, 199, 521, 2207, 3571, \ldots$ and the corresponding indices are
$0, 2, 4, 5, 7, 8, 11, 13, 16, 17, \ldots$. It is not known whether there are infinitely many
Lucas primes.

*References:*
- [Wikipedia: Lucas number, § Lucas primes](https://en.wikipedia.org/wiki/Lucas_number#Lucas_primes)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [OEIS A005479](https://oeis.org/A005479): the Lucas primes
- [OEIS A001606](https://oeis.org/A001606): indices $n$ such that $L_n$ is prime
-/

namespace LucasPrime

/--
**Lucas primes.** Are there infinitely many Lucas primes?

A Lucas prime is a Lucas number that is prime, where the Lucas numbers are given by
$L_0 = 2$, $L_1 = 1$ and $L_{n+2} = L_{n+1} + L_n$. The first few Lucas primes are
$2, 3, 7, 11, 29, 47, 199, 521, 2207, 3571, 9349, \ldots$
([OEIS A005479](https://oeis.org/A005479)); in particular $L_0 = 2$ is counted.
The question asks whether the set of prime numbers that occur as a Lucas number is infinite.
-/
theorem lucas_prime :
    {p : ℕ | p.Prime ∧ ∃ n, lucasNumber n = p}.Infinite := by
  sorry

end LucasPrime

theorem LucasPrime.lucas_prime.disproof : ¬ (type_of% @LucasPrime.lucas_prime) := sorry
