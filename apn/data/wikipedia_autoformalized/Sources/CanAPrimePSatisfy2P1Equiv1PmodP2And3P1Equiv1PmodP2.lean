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
* [OEIS A001220](https://oeis.org/A001220) (Wieferich primes)
* [OEIS A014127](https://oeis.org/A014127) (Mirimanoff primes)
-/

namespace CanAPrimePSatisfy2P1Equiv1PmodP2And3P1Equiv1PmodP2

/--
Can a prime $p$ satisfy $2^{p-1} \equiv 1 \pmod{p^2}$ and $3^{p-1} \equiv 1 \pmod{p^2}$
simultaneously? That is, does there exist a prime $p$ that is both a Wieferich prime and a
Mirimanoff prime?
-/
@[category research open, AMS 11]
theorem can_a_prime_p_satisfy_2_p_1_equiv_1_pmod_p_2_and_3_p_1_equiv_1_pmod_p_2 :
    answer(sorry) ↔
      ∃ p : ℕ, p.Prime ∧ 2 ^ (p - 1) ≡ 1 [MOD p ^ 2] ∧ 3 ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  sorry

/-- The prime $1093$ is a Wieferich prime: $2^{1092} \equiv 1 \pmod{1093^2}$. -/
@[category test, AMS 11]
theorem two_pow_modEq_one_1093 : 2 ^ (1093 - 1) ≡ 1 [MOD 1093 ^ 2] := by
  decide +kernel

/-- The prime $11$ is a Mirimanoff prime: $3^{10} \equiv 1 \pmod{11^2}$. -/
@[category test, AMS 11]
theorem three_pow_modEq_one_11 : 3 ^ (11 - 1) ≡ 1 [MOD 11 ^ 2] := by
  decide

/-- The prime $11$ is not a Wieferich prime: $2^{10} \not\equiv 1 \pmod{11^2}$. -/
@[category test, AMS 11]
theorem not_two_pow_modEq_one_11 : ¬ 2 ^ (11 - 1) ≡ 1 [MOD 11 ^ 2] := by
  decide

/-- The primes $2$ and $3$ satisfy neither congruence, so no hypothesis excluding them is needed
in the statement of the problem. -/
@[category test, AMS 11]
theorem not_modEq_two_three :
    ¬ 2 ^ (2 - 1) ≡ 1 [MOD 2 ^ 2] ∧ ¬ 3 ^ (2 - 1) ≡ 1 [MOD 2 ^ 2] ∧
      ¬ 2 ^ (3 - 1) ≡ 1 [MOD 3 ^ 2] ∧ ¬ 3 ^ (3 - 1) ≡ 1 [MOD 3 ^ 2] := by
  decide

end CanAPrimePSatisfy2P1Equiv1PmodP2And3P1Equiv1PmodP2
