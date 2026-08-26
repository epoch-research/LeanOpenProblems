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

/--
Let $f(n)$ be minimal such that any $f(n)$ points in $ℝ^2$, no three on a line,
contain $n$ points which form the vertices of a convex $n$-gon.
Prove that $f(n) = 2^{n-2} + 1$.
-/
theorem erdos_107 : ∀ n ≥ 3, f n = 2^(n - 2) + 1 := by
  sorry

namespace variants

end Erdos107.variants
