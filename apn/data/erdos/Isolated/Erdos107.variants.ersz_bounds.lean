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
Erdős and Szekeres proved the bounds
$$
  2^{n-2} + 1 ≤ f(n) ≤ \binom{2n-4}{n-2} + 1
$$
([ErSz60] and [ErSz35] respectively).

[ErSz60] Erdős, P. and Szekeres, G., _On some extremum problems in elementary geometry_.
  Ann. Univ. Sci. Budapest. Eötvös Sect. Math. (1960/61), 53-62.

[ErSz35] Erdős, P. and Szekeres, G., _A combinatorial problem in geometry_.
  Compos. Math. (1935), 463-470.
-/
theorem ersz_bounds :
    ∀ n ≥ 3, 2^(n - 2) + 1 ≤ f n ∧ f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1 := by
  sorry

end Erdos107.variants
