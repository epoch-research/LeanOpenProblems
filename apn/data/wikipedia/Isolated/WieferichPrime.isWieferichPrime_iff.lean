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

A Wieferich prime is a prime $p$ with $2^{p-1} \equiv 1 \pmod{p^2}$. The only known examples are
$1093$ and $3511$. It is conjectured that there are infinitely many Wieferich primes; a heuristic
argument suggests that the number of Wieferich primes up to $x$ grows like $\log \log x$.

More generally, a prime $p$ is a Wieferich prime to base $a$ if $a^{p-1} \equiv 1 \pmod{p^2}$.
Wikipedia's list of unsolved problems also asks whether there are infinitely many Wieferich primes
to every base $a > 0$, and whether there is any Wieferich prime to base $47$. It is also not known
whether there is any Wieferich prime besides $1093$ and $3511$.

*References:*
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [Wikipedia, Wieferich prime](https://en.wikipedia.org/wiki/Wieferich_prime)
* [OEIS A001220](https://oeis.org/A001220)
* P. Ribenboim, *Die Welt der Primzahlen*, 2nd ed., Springer (2006), pp. 242–243.
* [PrimeGrid, Wieferich and Wall–Sun–Sun Prime Search](https://www.primegrid.com/stats_ww.php)
-/

namespace WieferichPrime

/--
Are $1093$ and $3511$ the only Wieferich primes? They are the only known ones: PrimeGrid's search,
completed in 2022, shows that any other Wieferich prime exceeds $2^{64}$. On the other hand, the
heuristic count of $\log \log x$ Wieferich primes up to $x$ predicts that there are infinitely
many, see `infinite_isWieferichPrime`.
-/
theorem isWieferichPrime_iff :
    ∀ p, IsWieferichPrime p ↔ p = 1093 ∨ p = 3511 := by
  sorry

end WieferichPrime

theorem WieferichPrime.isWieferichPrime_iff.disproof : ¬ (type_of% @WieferichPrime.isWieferichPrime_iff) := sorry
