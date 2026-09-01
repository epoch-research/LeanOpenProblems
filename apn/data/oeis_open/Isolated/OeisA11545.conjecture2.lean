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
# $a(n)$ is the integer whose decimal digits are the first $n+1$ decimal digits of $\pi$

*References:*
- [A011545](https://oeis.org/A011545)
-/

namespace OeisA11545

open Real Int

/-- a n is the integer whose decimal digits are the first $n+1$ decimal digits of $\pi$. -/
noncomputable def a (n : ℕ) : ℕ :=
  (floor (Real.pi * (10 : ℝ) ^ n.cast)).toNat

/--
Number of collisions occurring in a system consisting of an infinitely massive,
rigid wall at the origin, a ball with mass m stationary at position $x_1 > 0$,
and a ball with mass $(10^2n)m$ at position $x_2 > x_1$ and rolling toward the origin,
assuming perfectly elastic collisions and no friction.

Strictly speaking, this property, which is equivalent to the statement that the interval
$(m\pi, \pi/\textrm{arctan}(1/m))$ does not contain an integer for all $m = 10^n$, is not
known to be true for sure. In other words, we do not know for certain that A332045 does not
contain a power of $10$.
-/
theorem conjecture2 :
    ∀ n : ℕ, ¬ ∃ (k : ℤ),
      (Real.pi * (10 : ℝ) ^ n.cast < k.cast) ∧
      (k.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast)) := by
  sorry

end OeisA11545

theorem OeisA11545.conjecture2.disproof : ¬ (type_of% @OeisA11545.conjecture2) := sorry
