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
# Infinitude of Lucas–Wieferich primes

*References:*
- [Wikipedia, Lucas–Wieferich prime](https://en.wikipedia.org/wiki/Lucas%E2%80%93Wieferich_prime)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Wall–Sun–Sun prime](https://en.wikipedia.org/wiki/Wall%E2%80%93Sun%E2%80%93Sun_prime)
- [OEIS A238736](https://oeis.org/A238736) (Pell–Wieferich primes)

Let $P$ and $Q$ be integers and let $U_n(P, Q)$ be the Lucas sequence of the first kind,
$U_0 = 0$, $U_1 = 1$, $U_{n+2} = P U_{n+1} - Q U_n$, with discriminant $D = P^2 - 4Q$.
A *Lucas–Wieferich prime* associated with the pair $(P, Q)$ is an odd prime $p$ not dividing $D$
such that $U_{p - \varepsilon}(P, Q) \equiv 0 \pmod{p^2}$, where
$\varepsilon = \left(\frac{D}{p}\right)$ is the Legendre symbol. This is `IsLucasWieferichPrime`.
The conditions that $p$ is odd and $p \nmid D$ exclude only finitely many primes for a fixed pair
$(P, Q)$, so they do not affect questions of infinitude.

The list of unsolved problems asks: for any given integer $a > 0$, are there infinitely many
Lucas–Wieferich primes associated with the pair $(a, -1)$? For $a = 1$ the sequence
$U_n(1, -1)$ is the Fibonacci sequence and these are the Fibonacci–Wieferich (Wall–Sun–Sun)
primes; for $a = 2$ the sequence $U_n(2, -1)$ is the Pell sequence and these are the
Pell–Wieferich primes.
-/

open scoped NumberTheorySymbols

namespace LucasWieferichPrime

/--
The case $a = 2$: are there infinitely many Lucas–Wieferich primes associated with the pair
$(2, -1)$? Here $U_n(2, -1) = P_n$ is the Pell sequence and the discriminant is $8$, so these
are the Pell–Wieferich primes, i.e. the odd primes $p$ with
$p^2 \mid P_{p - \left(\frac{8}{p}\right)}$. The known Pell–Wieferich primes are $13$, $31$ and
$1546463$ ([OEIS A238736](https://oeis.org/A238736)).
-/
theorem lucas_wieferich_prime.variants.pell_wieferich :
    {p : ℕ | IsLucasWieferichPrime 2 (-1) p}.Infinite := by
  sorry

end LucasWieferichPrime

theorem LucasWieferichPrime.lucas_wieferich_prime.variants.pell_wieferich.disproof : ¬ (type_of% @LucasWieferichPrime.lucas_wieferich_prime.variants.pell_wieferich) := sorry
