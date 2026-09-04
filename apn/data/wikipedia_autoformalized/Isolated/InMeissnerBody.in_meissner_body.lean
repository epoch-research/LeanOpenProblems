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
# Meissner bodies: the Bonnesen–Fenchel conjecture

The *Reuleaux tetrahedron* is the intersection of the four closed balls of radius $w$ centred at
the vertices of a regular tetrahedron of side length $w$. Unlike the Reuleaux triangle, it does
not have constant width. Meissner and Schilling showed how to modify it into a body of constant
width $w$: three of its six curved edges are cut off along the planes of the two adjacent faces of
the tetrahedron and replaced by pieces of a surface of revolution (a spindle) about the
corresponding edge of the tetrahedron. The three edges must be pairwise non-opposite, so they
either share a vertex or form a face, and there result two noncongruent bodies of constant width,
the two *Meissner tetrahedra* (or *Meissner bodies*). Both have the same volume, approximately
$0.41986\,w^3$.

Bonnesen and Fenchel conjectured that the Meissner tetrahedra have the least volume among all
three-dimensional convex bodies of the same constant width. This is the three-dimensional case of
the Blaschke–Lebesgue problem (solved in the plane by the Reuleaux triangle) and is still open.

*References:*
- [Wikipedia, Meissner body](https://en.wikipedia.org/wiki/Meissner_body)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- T. Bonnesen, W. Fenchel, *Theorie der konvexen Körper*, Springer, 1934.
- B. Kawohl, C. Weber, *Meissner's Mysterious Bodies*, Math. Intelligencer 33 (2011).
- H. Anciaux, B. Guilfoyle, *On the three-dimensional Blaschke–Lebesgue problem*,
  Proc. Amer. Math. Soc. 139 (2011), [arXiv:0906.3217](https://arxiv.org/abs/0906.3217).
-/

open MeasureTheory
open scoped EuclideanGeometry InnerProductSpace

namespace InMeissnerBody

/-- The width of a set $K \subseteq \mathbb{R}^3$ in the direction $u$:
$$\sup_{x \in K} \langle x, u\rangle - \inf_{x \in K} \langle x, u\rangle.$$
For a compact convex $K$ and a unit vector $u$ this is the distance between the two supporting
planes of $K$ orthogonal to $u$. (It is only meaningful for nonempty bounded $K$, e.g. convex
bodies; the statements below only apply it to such sets.) -/
noncomputable def width (K : Set ℝ³) (u : ℝ³) : ℝ :=
  sSup ((fun x => ⟪x, u⟫_ℝ) '' K) - sInf ((fun x => ⟪x, u⟫_ℝ) '' K)

/-- A set $K \subseteq \mathbb{R}^3$ has constant width $w$ if its width in every direction (every
unit vector) is $w$. -/
def HasConstantWidth (K : Set ℝ³) (w : ℝ) : Prop :=
  ∀ u : ℝ³, ‖u‖ = 1 → width K u = w

/-- The points `v 0`, `v 1`, `v 2`, `v 3` are the vertices of a regular tetrahedron of side
length `w`, i.e. they are pairwise at distance `w`. -/
def IsRegularTetrahedron (v : Fin 4 → ℝ³) (w : ℝ) : Prop :=
  ∀ i j, i ≠ j → dist (v i) (v j) = w

/-- The Reuleaux tetrahedron on the vertices `v` of a regular tetrahedron of side length `w`: the
intersection of the four closed balls of radius `w` centred at the vertices. -/
def reuleauxTetrahedron (v : Fin 4 → ℝ³) (w : ℝ) : Set ℝ³ :=
  ⋂ i, Metric.closedBall (v i) w

/-- The closed wedge of the tetrahedron `v` at its edge `v i v j`: the points whose barycentric
coordinates with respect to the two vertices other than `v i` and `v j` are both nonpositive.
This is the region between the planes of the two faces of the tetrahedron containing the edge
`v i v j`, on the far side of both faces; it contains the curved edge of the Reuleaux
tetrahedron joining `v i` and `v j`. -/
def edgeWedge (v : Fin 4 → ℝ³) (i j : Fin 4) : Set ℝ³ :=
  {x | ∃ a : Fin 4 → ℝ, ∑ m, a m = 1 ∧ (∀ m, m ≠ i → m ≠ j → a m ≤ 0) ∧ x = ∑ m, a m • v m}

/-- The spindle at the edge `v i v j`: the intersection of all closed balls of radius `w` whose
centres are at distance `w` from both `v i` and `v j`. These centres form a circle in the plane
perpendicular to the edge `v i v j` through its midpoint (the circle contains the opposite curved
edge of the Reuleaux tetrahedron), so the spindle is a solid of revolution about the line
`v i v j`, bounded by the surface swept out by a circular arc of radius `w` joining `v i`
and `v j`. -/
def edgeSpindle (v : Fin 4 → ℝ³) (w : ℝ) (i j : Fin 4) : Set ℝ³ :=
  {x | ∀ y, dist y (v i) = w → dist y (v j) = w → dist x y ≤ w}

/-- The Reuleaux tetrahedron on `v` in which the curved edges `v i v j` for `(i, j) ∈ edges` have
been rounded off in Meissner's way: inside the wedge at each such edge, the Reuleaux tetrahedron
is replaced by the spindle at that edge; outside these wedges it is left unchanged. -/
def roundedReuleauxTetrahedron (v : Fin 4 → ℝ³) (w : ℝ) (edges : Set (Fin 4 × Fin 4)) :
    Set ℝ³ :=
  reuleauxTetrahedron v w ∩ ⋂ e ∈ edges, ((edgeWedge v e.1 e.2)ᶜ ∪ edgeSpindle v w e.1 e.2)

/-- The Meissner tetrahedron of the first kind on the regular tetrahedron `v` of side length `w`:
the three rounded edges share the vertex `v 0`. -/
def meissnerBodyVertex (v : Fin 4 → ℝ³) (w : ℝ) : Set ℝ³ :=
  roundedReuleauxTetrahedron v w {(0, 1), (0, 2), (0, 3)}

/-- The Meissner tetrahedron of the second kind on the regular tetrahedron `v` of side length
`w`: the three rounded edges form the face `v 1 v 2 v 3`. -/
def meissnerBodyFace (v : Fin 4 → ℝ³) (w : ℝ) : Set ℝ³ :=
  roundedReuleauxTetrahedron v w {(1, 2), (1, 3), (2, 3)}

/--
**Bonnesen–Fenchel conjecture** (the three-dimensional Blaschke–Lebesgue problem).
Are the two Meissner tetrahedra the minimum-volume three-dimensional shapes of constant width?

That is, does every convex body $K \subset \mathbb{R}^3$ of constant width $w$ satisfy
$\operatorname{vol}(K) \ge \operatorname{vol}(M_w)$, where $M_w$ is either of the two Meissner
tetrahedra of width $w$? The two Meissner tetrahedra have the same volume, so the statement
compares $K$ with both of them; the vertices `v` range over all regular tetrahedra of side $w$,
so every congruent copy of a Meissner tetrahedron is covered. The width has to be fixed since the
volume scales with the cube of the width; equivalently, the ratio of the volume of a body of
constant width to the volume of the ball of the same width is minimised by the Meissner tetrahedra.
-/
theorem in_meissner_body :
    ∀ w : ℝ, 0 < w → ∀ v : Fin 4 → ℝ³, IsRegularTetrahedron v w →
      ∀ K : ConvexBody ℝ³, HasConstantWidth K w →
        volume (meissnerBodyVertex v w) ≤ volume (K : Set ℝ³) ∧
        volume (meissnerBodyFace v w) ≤ volume (K : Set ℝ³) := by
  sorry

end InMeissnerBody

theorem InMeissnerBody.in_meissner_body.disproof : ¬ (type_of% @InMeissnerBody.in_meissner_body) := sorry
