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

open scoped Real

/--
A064313: Integer part of area of a regular polygon with $n$ sides each of length 1.
$$a(n) = \left\lfloor \frac{n}{4 \tan(\pi/n)} \right\rfloor = \left\lfloor \frac{n}{4} \cot\left(\frac{\pi}{n}\right) \right\rfloor$$
The sequence is formally defined for $n \ge 2$. We return $0$ for $n < 2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n ≥ 2 then
    let n_real : ℝ := n
    -- Area of a regular $n$-gon with side length 1 is $A = \frac{n}{4} \cot(\frac{\pi}{n})$.
    -- Since $n \ge 2$, $\pi/n \in (0, \pi/2]$, which implies $\cot(\pi/n) \ge 0$, so $\mathrm{area} \ge 0$.
    let area : ℝ := n_real / 4 * Real.cot (Real.pi / n_real)
    (Int.floor area).toNat
  else
    0

/--
Conjecture from OEIS A064313, entry %C:
Usually (perhaps always?) $\lfloor n^2/(4\pi) - \pi/12 \rfloor$ for a polygon of circumference $n$.
-/
theorem oeis_64313_conjecture_0 (n : ℕ) (hn : n ≥ 2) :
    a n = (Int.floor ((n : ℝ)^2 / (4 * Real.pi) - Real.pi / 12)).toNat := by
  sorry

theorem oeis_64313_conjecture_0.disproof : ¬ (type_of% @oeis_64313_conjecture_0) := sorry
