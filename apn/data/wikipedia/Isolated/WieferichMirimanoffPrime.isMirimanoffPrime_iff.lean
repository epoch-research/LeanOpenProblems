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
# Can a prime $p$ satisfy $2^{p-1} \equiv 1 \pmod{p^2}$ and $3^{p-1} \equiv 1 \pmod{p^2}$?

A prime $p$ with $2^{p-1} \equiv 1 \pmod{p^2}$ is a Wieferich prime (the only known examples
are $1093$ and $3511$). A prime $p$ with $3^{p-1} \equiv 1 \pmod{p^2}$ is a Mirimanoff prime
(the only known examples are $11$ and $1006003$). It is an open question whether a prime can
satisfy both congruences simultaneously. Lenstra gave a heuristic argument against this.

*References:*
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [Wikipedia, Wieferich prime](https://en.wikipedia.org/wiki/Wieferich_prime)
* J. B. Dobson, [On Lerch's formula for the Fermat quotient](https://arxiv.org/abs/1103.3907v6)
* F. G. Dorais and D. Klyve, [A Wieferich prime search up to $6.7 \times 10^{15}$](https://cs.uwaterloo.ca/journals/JIS/VOL14/Klyve/klyve3.html),
  J. Integer Seq. 14 (2011), Article 11.9.2.
* [OEIS A001220](https://oeis.org/A001220) (Wieferich primes)
* [OEIS A014127](https://oeis.org/A014127) (Mirimanoff primes)
-/

namespace WieferichMirimanoffPrime

/--
Are $11$ and $1006003$ the only Mirimanoff primes? They are the only known ones: Dorais and Klyve
found no other below $9.7 \times 10^{14}$.
-/
theorem isMirimanoffPrime_iff :
    ∀ p, IsMirimanoffPrime p ↔ p = 11 ∨ p = 1006003 := by
  sorry

end WieferichMirimanoffPrime

theorem WieferichMirimanoffPrime.isMirimanoffPrime_iff.disproof : ¬ (type_of% @WieferichMirimanoffPrime.isMirimanoffPrime_iff) := sorry
