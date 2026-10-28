/-
Copyright 2025 The Formal Conjectures Authors.

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
# Infinitude of Wall–Sun–Sun primes

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Wall%E2%80%93Sun%E2%80%93Sun_prime)
- [EJ10] A.-S. Elsenhans and J. Jahnel, *The Fibonacci sequence modulo $p^2$ – An investigation by
  computer for $p < 10^{14}$*, [arXiv:1006.0824](https://arxiv.org/abs/1006.0824)
-/

open Algebra (IsQuadraticExtension)
open NumberField

namespace QuadraticAlgebra
variable {d : ℤ} [Fact <| Squarefree d] [Fact <| d ≠ 1]

end QuadraticAlgebra

namespace Algebra
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

end Algebra

namespace NumberField
variable {K : Type*} [Field K] [NumberField K]

end NumberField

namespace WallSunSun

open scoped NumberTheorySymbols

/--
Let $K$ be a real quadratic field of discriminant $D$ and let $\varepsilon$ be a fundamental unit
of $K$. Following [EJ10, Remark 2.2.8], an odd prime $p \nmid D$ is a Wall–Sun–Sun prime for $K$
if, in $\mathcal{O}_K$, $\varepsilon^{p-1} \equiv 1 \pmod{p^2}$ when
$\left(\tfrac{D}{p}\right) = 1$, and $\varepsilon^{2p+2} \equiv 1 \pmod{p^2}$ when
$\left(\tfrac{D}{p}\right) = -1$. Both exponents are even, so the condition does not depend on the
choice of $\varepsilon$, and it is equivalent to asking the same congruence for every unit of $K$.
For $K = \mathbb{Q}(\sqrt{5})$ and $\varepsilon = \frac{1 + \sqrt{5}}{2}$ these are the classical
Wall–Sun–Sun primes other than $2$ and $5$ [EJ10, Proposition 2.2.6].

It is conjectured that for every fundamental discriminant $D \neq 1$ there are infinitely many
Wall–Sun–Sun primes with discriminant $D$ (Wikipedia; [EJ10, §4.1] gives the heuristic for
$\mathbb{Q}(\sqrt{5})$). It is stated here for $D > 0$ only. Wikipedia's sentence also covers
$D < 0$, but [EJ10] gives the definition above only for real quadratic fields, and its literal
extension to imaginary quadratic fields is degenerate: there every unit is a root of unity of
order dividing $4$ or $6$, and that order divides the relevant exponent $p - 1$ or $2p + 2$ for
every odd prime $p \nmid D$.
-/
theorem infinite_isWallSunSunPrime_of_disc_eq {K : Type*} [Field K] [NumberField K]
    [IsQuadraticExtension ℚ K] [IsTotallyReal K] {D : ℤ} (hD : discr K = D) :
    {p : ℕ | p.Prime ∧ Odd p ∧ ¬ (p : ℤ) ∣ D ∧ ∀ ε : (𝓞 K)ˣ,
      (p : 𝓞 K) ^ 2 ∣ (ε : 𝓞 K) ^ (if J(D | p) = 1 then p - 1 else 2 * p + 2) - 1}.Infinite := by
  sorry

end WallSunSun

theorem WallSunSun.infinite_isWallSunSunPrime_of_disc_eq.disproof : ¬ (type_of% @WallSunSun.infinite_isWallSunSunPrime_of_disc_eq) := sorry
