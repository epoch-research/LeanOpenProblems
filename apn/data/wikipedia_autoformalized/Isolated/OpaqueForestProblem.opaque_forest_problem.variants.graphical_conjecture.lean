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
# Opaque forest problem

An *opaque set* (or *barrier*, *opaque cover*) for a planar set $K$ is a set $B$ in the plane
that meets every line meeting $K$. The opaque forest problem asks for the shortest opaque set
of a given shape, where the length of an arbitrary set is its one-dimensional Hausdorff
measure $\mathcal{H}^1$. The barrier is unrestricted in location (it may lie outside $K$) and
need not be connected.

*References:*
- [Wikipedia, Opaque forest problem](https://en.wikipedia.org/wiki/Opaque_forest_problem)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [DJP14] Dumitrescu, A., Jiang, M., Pach, J., _Opaque sets_. Algorithmica 69 (2014), 315–334.
  [arXiv:1005.2218](https://arxiv.org/abs/1005.2218)
- [DJ14] Dumitrescu, A., Jiang, M., _The opaque square_. Proc. 30th Annual Symposium on
  Computational Geometry (SoCG'14). [arXiv:1311.3323](https://arxiv.org/abs/1311.3323)
- [PBTW12] Provan, J. S., Brazil, M., Thomas, D. A., Weng, J. F., _Minimum opaque covers for
  polygonal regions_. [arXiv:1210.8139](https://arxiv.org/abs/1210.8139)
- [Iz16] Izumi, T., _Improving the lower bound on opaque sets for equilateral triangle_.
  Discrete Applied Mathematics 213 (2016), 130–138.
-/

open EuclideanGeometry MeasureTheory
open scoped ENNReal

namespace OpaqueForestProblem

/--
A set `B` in the plane is an *opaque set* (or *barrier*) for the set `K` if every line in the
plane that meets `K` also meets `B`. A line is an affine subspace of `ℝ²` whose direction is
one-dimensional. No restriction is placed on `B`: it may lie outside `K` and need not be
connected.
-/
def IsOpaqueSet (K B : Set ℝ²) : Prop :=
  ∀ L : AffineSubspace ℝ ℝ², Module.finrank ℝ L.direction = 1 →
    (K ∩ L).Nonempty → (B ∩ L).Nonempty

/--
The set of lengths of all opaque sets for `K`, where the length of an arbitrary set is its
one-dimensional Hausdorff measure $\mathcal{H}^1$ (which agrees with the usual length for line
segments and rectifiable curves).
-/
noncomputable def opaqueLengths (K : Set ℝ²) : Set ℝ≥0∞ :=
  μH[1] '' {B | IsOpaqueSet K B}

/-- A set is a *finite union of line segments* if it is the union of finitely many (closed)
line segments. Following [PBTW12], such opaque sets are called *graphical*. -/
def IsFiniteUnionOfSegments (B : Set ℝ²) : Prop :=
  ∃ S : Finset (ℝ² × ℝ²), B = ⋃ e ∈ S, segment ℝ e.1 e.2

/-- The unit square $[0, 1]^2$, as the convex hull of its four corners. -/
def unitSquare : Set ℝ² :=
  convexHull ℝ {!₂[0, 0], !₂[1, 0], !₂[0, 1], !₂[1, 1]}

/--
**The Graphical Conjecture** of Provan, Brazil, Thomas and Weng [PBTW12].
Every convex polygon (the convex hull of finitely many points of the plane, with nonempty
interior) has a shortest opaque set that is *graphical*, i.e. a finite union of line segments
(an opaque forest). In other words, some finite union of line segments is an opaque set for the
polygon whose length ($\mathcal{H}^1$-measure) is at most the length of every other opaque set
for the polygon. In particular every convex polygon has a shortest opaque set.
Following [PBTW12], no acyclicity condition is imposed on the union of segments.
-/
theorem opaque_forest_problem.variants.graphical_conjecture (V : Finset ℝ²)
    (hV : (interior (convexHull ℝ (V : Set ℝ²))).Nonempty) :
    ∃ B, IsFiniteUnionOfSegments B ∧ IsOpaqueSet (convexHull ℝ (V : Set ℝ²)) B ∧
      ∀ B', IsOpaqueSet (convexHull ℝ (V : Set ℝ²)) B' → μH[1] B ≤ μH[1] B' := by
  sorry

end OpaqueForestProblem

theorem OpaqueForestProblem.opaque_forest_problem.variants.graphical_conjecture.disproof : ¬ (type_of% @OpaqueForestProblem.opaque_forest_problem.variants.graphical_conjecture) := sorry
