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
# Ehrhart's volume conjecture

Ehrhart's volume conjecture gives an upper bound on the volume of a convex body in $\mathbb{R}^n$
whose barycenter is its only interior lattice point. It is a kind of converse to Minkowski's
theorem on centrally symmetric convex bodies.

*References:*
- [Wikipedia, Ehrhart's volume conjecture](https://en.wikipedia.org/wiki/Ehrhart%27s_volume_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- B. Nill, A. Paffenholz, *On the equality case in Ehrhart's volume conjecture*,
  Adv. Geom. 14 (2014), [arXiv:1205.1270](https://arxiv.org/abs/1205.1270)
-/

open MeasureTheory

open scoped EuclideanGeometry Nat

namespace EhrhartsVolumeConjecture

/-- A point of $\mathbb{R}^n$ is a *lattice point* if all of its coordinates are integers,
i.e. if it lies in $\mathbb{Z}^n$. -/
def IsLatticePoint {n : ℕ} (x : ℝ^n) : Prop :=
  ∀ i, ∃ k : ℤ, x i = k

/--
**Ehrhart's volume conjecture.**
A convex body $K$ in $n$ dimensions containing a single lattice point in its interior as its
center of mass cannot have volume greater than $(n+1)^n / n!$, i.e.
$$\operatorname{Vol}(K) \le \frac{(n+1)^n}{n!}.$$

Here a convex body is a nonempty compact convex subset of $\mathbb{R}^n$ (`ConvexBody`), and the
center of mass (barycenter) of $K$ is $\frac{1}{\operatorname{Vol}(K)} \int_K x \, dx$, written
`⨍ x in K, x`. The hypothesis says that the set of lattice points in the interior of $K$ is
exactly the singleton consisting of the barycenter of $K$; in particular the interior of $K$ is
nonempty, so $K$ is $n$-dimensional and has positive finite volume.
-/
theorem ehrharts_volume_conjecture (n : ℕ) (hn : 0 < n) (K : ConvexBody (ℝ^n))
    (hK : {x ∈ interior (K : Set (ℝ^n)) | IsLatticePoint x} = {⨍ x in (K : Set (ℝ^n)), x}) :
    volume (K : Set (ℝ^n)) ≤ (n + 1) ^ n / n ! := by
  sorry

end EhrhartsVolumeConjecture

theorem EhrhartsVolumeConjecture.ehrharts_volume_conjecture.disproof : ¬ (type_of% @EhrhartsVolumeConjecture.ehrharts_volume_conjecture) := sorry
