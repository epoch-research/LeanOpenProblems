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
Wolfgang Haken (1977) conjectured that no term of this sequence is a perfect square,
and estimated the probability that this conjecture is false to be smaller than $10^-9$.
-/
theorem conjecture1 : ∀ n, ¬ IsSquare (a n) := by
  sorry

end OeisA11545

theorem OeisA11545.conjecture1.disproof : ¬ (type_of% @OeisA11545.conjecture1) := sorry
