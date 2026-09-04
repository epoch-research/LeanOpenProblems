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

/-- Every set is an opaque set for itself. -/
@[category API, AMS 52]
theorem isOpaqueSet_self (K : Set ℝ²) : IsOpaqueSet K K :=
  fun _ _ h => h

/-- Enlarging an opaque set keeps it opaque. -/
@[category API, AMS 52]
theorem IsOpaqueSet.mono {K B B' : Set ℝ²} (h : IsOpaqueSet K B) (hB : B ⊆ B') :
    IsOpaqueSet K B' :=
  fun L hL hK => (h L hL hK).mono (Set.inter_subset_inter_left _ hB)

/-- An opaque set for `K` is an opaque set for every subset of `K`. -/
@[category API, AMS 52]
theorem IsOpaqueSet.anti {K K' B : Set ℝ²} (h : IsOpaqueSet K B) (hK : K' ⊆ K) :
    IsOpaqueSet K' B :=
  fun L hL hK' => h L hL (hK'.mono (Set.inter_subset_inter_left _ hK))

/-- The length of `K` itself belongs to the set of lengths of opaque sets for `K`. -/
@[category test, AMS 52]
theorem hausdorffMeasure_mem_opaqueLengths (K : Set ℝ²) : μH[1] K ∈ opaqueLengths K :=
  ⟨K, isOpaqueSet_self K, rfl⟩

/-- A single line segment is a finite union of line segments. -/
@[category test, AMS 52]
theorem isFiniteUnionOfSegments_segment (p q : ℝ²) :
    IsFiniteUnionOfSegments (segment ℝ p q) :=
  ⟨{(p, q)}, by simp⟩

/-- The corner `(1, 1)` lies in the unit square. -/
@[category test, AMS 52]
theorem mem_unitSquare : !₂[1, 1] ∈ unitSquare :=
  subset_convexHull ℝ _ (by simp)

/--
**Opaque forest problem for the unit square.**
The shortest known opaque set for the unit square is the two-component forest of Jones and
Poirier: the minimum Steiner tree of three of the corners of the square together with the
segment from the fourth corner to the centre. It has length
$\sqrt{2} + \tfrac{1}{2}\sqrt{6} \approx 2.639$ and is conjectured to be optimal [DJP14, DJ14].
The conjecture: the infimum of the lengths ($\mathcal{H}^1$-measures) of all opaque sets for the
unit square equals $\sqrt{2} + \tfrac{1}{2}\sqrt{6}$. The barrier is unrestricted in location
and need not be connected. This is stated as an infimum rather than an attained minimum, since
the existence of a shortest opaque set is itself open.
-/
@[category research open, AMS 52]
theorem opaque_forest_problem :
    IsGLB (opaqueLengths unitSquare) (ENNReal.ofReal (√2 + √6 / 2)) := by
  sorry

/--
**Existence of a shortest opaque set.**
Does every convex body $K$ in the plane (a compact convex set with nonempty interior) have a
shortest opaque set? That is, is there an opaque set for $K$ whose length
($\mathcal{H}^1$-measure) is at most the length of every other opaque set for $K$? The
alternative is that the lengths of the opaque sets for $K$ approach their infimum without ever
reaching it. The opaque sets range over arbitrary subsets of the plane and are unrestricted in
location. The nonempty interior excludes degenerate bodies (points and segments).
-/
@[category research open, AMS 52]
theorem opaque_forest_problem.variants.minimizer_exists :
    answer(sorry) ↔ ∀ K : Set ℝ², IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ B, IsOpaqueSet K B ∧ ∀ B', IsOpaqueSet K B' → μH[1] B ≤ μH[1] B' := by
  sorry

/--
**The Graphical Conjecture** of Provan, Brazil, Thomas and Weng [PBTW12].
Every convex polygon (the convex hull of finitely many points of the plane, with nonempty
interior) has a shortest opaque set that is *graphical*, i.e. a finite union of line segments
(an opaque forest). In other words, some finite union of line segments is an opaque set for the
polygon whose length ($\mathcal{H}^1$-measure) is at most the length of every other opaque set
for the polygon. In particular every convex polygon has a shortest opaque set.
Following [PBTW12], no acyclicity condition is imposed on the union of segments.
-/
@[category research open, AMS 52]
theorem opaque_forest_problem.variants.graphical_conjecture (V : Finset ℝ²)
    (hV : (interior (convexHull ℝ (V : Set ℝ²))).Nonempty) :
    ∃ B, IsFiniteUnionOfSegments B ∧ IsOpaqueSet (convexHull ℝ (V : Set ℝ²)) B ∧
      ∀ B', IsOpaqueSet (convexHull ℝ (V : Set ℝ²)) B' → μH[1] B ≤ μH[1] B' := by
  sorry

/--
**Opaque sets for the equilateral triangle.**
The shortest connected opaque set for a triangle is its minimum Steiner tree; for an
equilateral triangle of side length $1$ this tree consists of the three segments from the
vertices to the centre and has length $\sqrt{3}$. Without assuming connectivity, the
optimality of the Steiner tree has not been demonstrated [DJP14, PBTW12, Iz16]: the conjecture
is that the infimum of the lengths ($\mathcal{H}^1$-measures) of all opaque sets for an
equilateral triangle of side length $1$ equals $\sqrt{3}$. The barrier is unrestricted in
location and need not be connected.
-/
@[category research open, AMS 52]
theorem opaque_forest_problem.variants.equilateral_triangle (a b c : ℝ²)
    (hab : dist a b = 1) (hbc : dist b c = 1) (hca : dist c a = 1) :
    IsGLB (opaqueLengths (convexHull ℝ {a, b, c})) (ENNReal.ofReal √3) := by
  sorry

end OpaqueForestProblem
