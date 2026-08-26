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

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Wall%E2%80%93Sun%E2%80%93Sun_prime)
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

/-- Fundamental discriminants are those integers `D` that appear as discriminants of quadratic
fields.

`D` is a fundamental discriminant if it is either of the form `4m` for `m` congruent to `2` or `3`
mod `4` squarefree, or if it congruent to `1` mod `4` and squarefree. -/
def IsFundamentalDiscr (D : ℤ) : Prop :=
  4 ∣ D ∧ ¬ D / 4 ≡ 1 [ZMOD 4] ∧ Squarefree (D / 4) ∨ D ≠ 1 ∧ D ≡ 1 [ZMOD 4] ∧ Squarefree D

end NumberField

namespace WallSunSun

/--
A Lucas–Wieferich prime associated with $(a,b)$ is an odd prime $p$, not dividing $a^2 - 4b$, such
that $U_{p-\varepsilon}(a,b) \equiv 0 \pmod{p^2}$ where $U(a,b)$ is the Lucas sequence of the first
kind and $\varepsilon$ is the Legendre symbol $\left({\tfrac {a^2-4b}{p}}\right)$.
The discriminant of this number is the quantity $a^2 - 4b$. It is conjectured that there are
infinitely many Lucas–Wieferich primes of any given non-one fundamental discriminant.

TODO: Source this conjecture
-/
theorem infinite_isWallSunSunPrime_of_disc_eq {D : ℤ} (hD : IsFundamentalDiscr D)
    (hD₁ : D ≠ 1) :
    {p : ℕ | ∃ a b, a ^ 2 - 4 * b = D ∧ IsLucasWieferichPrime a b p}.Infinite := by
  sorry

end WallSunSun
