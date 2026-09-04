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
For any given integer $a > 0$, are there infinitely many Lucas–Wieferich primes associated with
the pair $(a, -1)$? Such a prime is an odd prime $p$ with $p \nmid a^2 + 4$ and
$U_{p - \varepsilon}(a, -1) \equiv 0 \pmod{p^2}$, where $U(a, -1)$ is the Lucas sequence of the
first kind with $U_{n+2} = a U_{n+1} + U_n$ and $\varepsilon = \left(\frac{a^2 + 4}{p}\right)$.
The question is read as a single yes/no question: is the answer "yes" for every $a > 0$?
-/
@[category research open, AMS 11]
theorem lucas_wieferich_prime :
    answer(sorry) ↔
      ∀ a : ℤ, 0 < a → {p : ℕ | IsLucasWieferichPrime a (-1) p}.Infinite := by
  sorry

/--
The case $a = 1$: are there infinitely many Lucas–Wieferich primes associated with the pair
$(1, -1)$? Here $U_n(1, -1) = F_n$ is the Fibonacci sequence and the discriminant is $5$, so
these are the Fibonacci–Wieferich primes, i.e. the Wall–Sun–Sun primes $p \ne 2, 5$ with
$p^2 \mid F_{p - \left(\frac{5}{p}\right)}$. No such prime is known.

This is the question `WallSunSun.infinite_isWallSunSunPrime` of
`FormalConjectures.Wikipedia.WallSunSun`, which is stated with the equivalent Lucas-number
criterion $L_p \equiv 1 \pmod{p^2}$; see
`LucasWieferichPrime.isLucasWieferichPrime_one_neg_one_iff_isWallSunSunPrime`.
-/
@[category research open, AMS 11]
theorem lucas_wieferich_prime.variants.fibonacci_wieferich :
    answer(sorry) ↔ {p : ℕ | IsLucasWieferichPrime 1 (-1) p}.Infinite := by
  sorry

/--
The case $a = 2$: are there infinitely many Lucas–Wieferich primes associated with the pair
$(2, -1)$? Here $U_n(2, -1) = P_n$ is the Pell sequence and the discriminant is $8$, so these
are the Pell–Wieferich primes, i.e. the odd primes $p$ with
$p^2 \mid P_{p - \left(\frac{8}{p}\right)}$. The known Pell–Wieferich primes are $13$, $31$ and
$1546463$ ([OEIS A238736](https://oeis.org/A238736)).
-/
@[category research open, AMS 11]
theorem lucas_wieferich_prime.variants.pell_wieferich :
    answer(sorry) ↔ {p : ℕ | IsLucasWieferichPrime 2 (-1) p}.Infinite := by
  sorry

/--
The Lucas–Wieferich primes associated with $(1, -1)$ are exactly the Wall–Sun–Sun primes as
defined by the Lucas-number criterion $L_p \equiv 1 \pmod{p^2}$.

For an odd prime $p \ne 5$ this is the standard equivalence of the two definitions of a
Wall–Sun–Sun prime, $p^2 \mid F_{p - \left(\frac{5}{p}\right)}$ and $L_p \equiv 1 \pmod{p^2}$.
Neither side holds for $p = 2$ or $p = 5$: the primes $2$ and $5$ are excluded from
`IsLucasWieferichPrime 1 (-1)` (as $2$ is even and $5 \mid 5$), while $L_2 = 3 \not\equiv 1
\pmod 4$ and $L_5 = 11 \not\equiv 1 \pmod{25}$.
-/
@[category textbook, AMS 11]
theorem isLucasWieferichPrime_one_neg_one_iff_isWallSunSunPrime (p : ℕ) :
    IsLucasWieferichPrime 1 (-1) p ↔ IsWallSunSunPrime p := by
  sorry

/-- The Lucas sequence $U(1, -1)$ is the Fibonacci sequence. -/
@[category test, AMS 11]
theorem lucasSequence_U_one_neg_one (n : ℕ) : LucasSequence.U 1 (-1) n = Nat.fib n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [LucasSequence.U]
  | one => simp [LucasSequence.U]
  | more n ih₁ ih₂ => simp [LucasSequence.U, Nat.fib_add_two, ih₁, ih₂, add_comm]

/-- $13$ is a Pell–Wieferich prime: $\left(\frac{8}{13}\right) = -1$ and
$13^2 \mid P_{14} = 80782$. -/
@[category test, AMS 11]
theorem isLucasWieferichPrime_two_neg_one_thirteen : IsLucasWieferichPrime 2 (-1) 13 := by
  refine ⟨by norm_num, by decide, by decide, ?_⟩
  have h : J(2 ^ 2 - 4 * -1 | 13) = -1 := by norm_num
  rw [h]
  decide

/-- $31$ is a Pell–Wieferich prime: $\left(\frac{8}{31}\right) = 1$ and
$31^2 \mid P_{30}$. -/
@[category test, AMS 11]
theorem isLucasWieferichPrime_two_neg_one_thirtyOne : IsLucasWieferichPrime 2 (-1) 31 := by
  refine ⟨by norm_num, by decide, by decide, ?_⟩
  have h : J(2 ^ 2 - 4 * -1 | 31) = 1 := by norm_num
  rw [h]
  decide

end LucasWieferichPrime
