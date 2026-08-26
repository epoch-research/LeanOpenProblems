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
# Erdős Problem 107

*References:*
- [erdosproblems.com/107](https://www.erdosproblems.com/107)
- [Wikipedia](https://en.wikipedia.org/wiki/Happy_ending_problem)
-/

open Filter
open EuclideanGeometry

namespace Erdos107

/-- The set of $N$ such that any $N$ points in the plane, no three on a line,
contain a convex $n$-gon. -/
def cardSet (n : ℕ) := { N | ∀ (pts : Finset ℝ²), pts.card = N → NonTrilinear (pts : Set ℝ²) →
  HasConvexNGon n pts }

/-- The function $f(n)$ specified in `erdos_107`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf (cardSet n)

namespace variants

/--
The current best bound is due to Holmsen, Mojarrad, Pach, and Tardos [HMPT20],
who prove
$$
  f(n) ≤ 2^{n+O(\sqrt{n\log n})}.
$$

[HMPT20] Holmsen, Andreas F. and Mojarrad, Hossein Nassajian and Pach, János and Tardos, Gábor,
  _Two extensions of the Erdős-Szekeres problem_. J. Eur. Math. Soc. (JEMS) (2020), 3981-3995.
-/
theorem hmpt_bound :
    ∃ r : ℕ → ℝ, r =O[atTop] (fun n => Real.sqrt (n * Real.log n)) ∧
      ∀ n ≥ 3, (f n : ℝ) ≤ 2^(n + r n) := by
  sorry

end Erdos107.variants

theorem Erdos107.variants.hmpt_bound.disproof : ¬ (type_of% @Erdos107.variants.hmpt_bound) := sorry
