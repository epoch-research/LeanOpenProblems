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
# Factorial distance to nearest square

The sequence is defined as
$$a(n) =
\mathrm{round}\left(\frac{\mathrm{round}(\sqrt{n!})}{\left|(\mathrm{round}(\sqrt{n!}))^2 -
n!\right|}\right)$$
for $n \ge 2$.

*References:*
- [A145355](https://oeis.org/A145355)
-/

namespace OeisA145355

open Real

/-- The sequence $a(n) = \mathrm{round}(\mathrm{round}(\sqrt{n!})/|(\mathrm{round}(\sqrt{n!}))^2 - n!|)$. -/
noncomputable def a (n : ℕ) : ℕ :=
  let fact_r : ℝ := Nat.cast (Nat.factorial n)
  let r_int : ℤ := round (sqrt fact_r)
  let r_real : ℝ := Int.cast r_int
  let den_val : ℝ := abs (r_real ^ 2 - fact_r)
  (round (r_real / den_val)).toNat

/--
This sequence suggests that the distance between a factorial and the closest power is
tightly bounded.
-/
theorem conjecture : ∃ C : ℕ, ∀ n : ℕ, 2 ≤ n → a n ≤ C := by
  sorry

end OeisA145355

theorem OeisA145355.conjecture.disproof : ¬ (type_of% @OeisA145355.conjecture) := sorry
