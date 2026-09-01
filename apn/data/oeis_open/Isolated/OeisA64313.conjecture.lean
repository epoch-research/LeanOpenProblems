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
# Integer part of area of a regular polygon with $n$ sides each of length 1

The area of a regular $n$-gon with side length 1 is given by
$\frac{n}{4} \cot(\pi / n) = \frac{n}{4 \tan(\pi / n)}$.

*References:*
- [A064313](https://oeis.org/A064313)
-/

namespace OeisA64313

/-- The exact area of a regular $n$-gon with side length 1. -/
noncomputable def area (n : ℕ) : ℝ :=
  (n : ℝ) / (4 * Real.tan (Real.pi / (n : ℝ)))

/-- Integer part of area of a regular polygon with $n$ sides each of length 1. -/
noncomputable def a (n : ℕ) : ℕ :=
  (Int.floor (area n)).toNat

/--
"Usually (perhaps always?) $\lfloor n^2 / (4\pi) - \pi / 12 \rfloor$ for a polygon of circumference $n$.
Note that the area of a circle with circumference $C$ is $C^2 / (4\pi)$."
-/
theorem conjecture (n : ℕ) (hn : 3 ≤ n) :
    a n = (Int.floor ((n : ℝ) ^ 2 / (4 * Real.pi) - Real.pi / 12)).toNat := by
  sorry

end OeisA64313

theorem OeisA64313.conjecture.disproof : ¬ (type_of% @OeisA64313.conjecture) := sorry
