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
# Nearest integer to $n/\sqrt{2}$

Nearest integer to $n/\sqrt{2}$, defined by $\lfloor n/\sqrt{2} + 1/2 \rfloor$.

*References:*
- [A049473](https://oeis.org/A049473)-/

namespace OeisA49473

/-- Nearest integer to $n/\sqrt{2}$. -/
noncomputable def a (n : ℕ) : ℕ :=
  (Int.floor ((n : ℝ) / Real.sqrt 2 + 1 / 2)).toNat

/-- $\zeta(3)$ (Apéry's constant). -/
noncomputable def zetaThreeReal : ℝ :=
  (riemannZeta 3).re

/-- Let $s(n) = \zeta(3) - \sum_{k=1}^{n} 1/k^3$. -/
noncomputable def s (n : ℕ) : ℝ :=
  zetaThreeReal - ∑ k ∈ Finset.range n, (1 : ℝ) / ((k + 1 : ℝ) ^ 3)

/-- A001953: Nonhomogeneous Beatty sequence $\lfloor (k + 1/2)\sqrt{2} \rfloor$ for $k \ge 0$. -/
def A001953 : Set ℕ :=
  {n | ∃ k : ℕ, n = (Int.floor (((k : ℝ) + 1 / 2) * Real.sqrt 2)).toNat}

/-- A001954: Nonhomogeneous Beatty sequence $\lfloor (k + 1/2)(2 + \sqrt{2}) \rfloor$ for $k \ge 0$. -/
def A001954 : Set ℕ :=
  {n | ∃ k : ℕ, n = (Int.floor (((k : ℝ) + 1 / 2) * (2 + Real.sqrt 2))).toNat}

/--
Let $s(n) = \zeta(3) - \sum_{k=1}^n \frac{1}{k^3}$.
Conjecture: for $n \ge 1$, $s(a(n)) < \frac{1}{n^2} < s(a(n)-1)$, and the difference sequence of
A049473 consists solely of $0$'s and $1$'s, in positions given by the nonhomogeneous Beatty
sequences A001954 and A001953, respectively.
- Clark Kimberling, Oct 05 2014
-/
theorem conjecture :
    (∀ n : ℕ, 1 ≤ n → s (a n) < 1 / (n : ℝ) ^ 2 ∧ 1 / (n : ℝ) ^ 2 < s (a n - 1)) ∧
    (∀ n : ℕ, 1 ≤ n →
      let diff : ℕ := a n - a (n - 1)
      (diff = 0 ↔ n - 1 ∈ A001954) ∧ (diff = 1 ↔ n - 1 ∈ A001953)) := by
  sorry

end OeisA49473

theorem OeisA49473.conjecture.disproof : ¬ (type_of% @OeisA49473.conjecture) := sorry
