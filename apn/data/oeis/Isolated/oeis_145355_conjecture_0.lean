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

import FormalConjectures.Util.ProblemImports

open Real

/--
A145355: $a(n) = \mathrm{round}(\mathrm{round}(\sqrt{n!})/|(\mathrm{round}(\sqrt{n!}))^2 - n!|)$.
The provided sequence starts at $n=2$. The definition works for $n=0, 1$ as well, provided we accept the behavior of $\mathbb{R}$ division by zero, which in Mathlib is typically $0$ but the result is not significant since the sequence is defined for $n \ge 2$ where the denominator is nonzero.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let fact_r : ℝ := Nat.cast (Nat.factorial n)
  let r_int : ℤ := round (sqrt fact_r)
  let r_real : ℝ := Int.cast r_int
  let den_val : ℝ := abs (r_real^2 - fact_r)
  (round (r_real / den_val)).toNat

/--
oeis_145355_conjecture_0: This sequence suggests that the distance between a factorial and the closest power is tightly bounded.

Formalization: The sequence $a(n)$ is bounded.
This is the most direct mathematical interpretation of the data provided for $a(n)$.
-/
theorem oeis_145355_conjecture_0 : ∃ C : ℕ, ∀ n : ℕ, 2 ≤ n → a n ≤ C := by
  sorry

theorem oeis_145355_conjecture_0.disproof : ¬ (type_of% @oeis_145355_conjecture_0) := sorry
