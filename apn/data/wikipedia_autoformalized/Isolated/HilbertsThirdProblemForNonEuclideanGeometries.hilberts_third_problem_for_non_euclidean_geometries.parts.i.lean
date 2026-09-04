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
# Hilbert's third problem for non-Euclidean geometries

Hilbert's third problem asks whether two Euclidean polyhedra of the same volume are always
scissors-congruent. Dehn answered it negatively with the Dehn invariant, and Sydler proved that
two Euclidean polyhedra are scissors-congruent if and only if they have the same volume and the
same Dehn invariant. Jessen asked whether the analogue of Sydler's theorem holds in spherical and
in hyperbolic geometry. Dehn's method still shows that scissors-congruent polyhedra have equal
Dehn invariants in these geometries, but the converse is open:

*In spherical or hyperbolic geometry, must polyhedra with the same volume and Dehn invariant be
scissors-congruent?*

The two geometries are formalised separately, in the namespaces `Spherical` and `Hyperbolic`.

## Models

* Spherical $3$-space is the unit sphere $S^3 \subseteq \mathbb{R}^4$. Its geodesic tetrahedra are
  the intersections of $S^3$ with the simplicial cones spanned by four linearly independent unit
  vectors; the volume is the surface measure of $S^3$ (`MeasureTheory.Measure.toSphere`); the
  isometry group is $O(4)$.
* Hyperbolic $3$-space is the upper sheet
  $H^3 = \{x \in \mathbb{R}^4 \mid \langle x, x\rangle = 1, x_0 > 0\}$ of the hyperboloid of the
  Minkowski form $\langle x, y\rangle = x_0 y_0 - x_1 y_1 - x_2 y_2 - x_3 y_3$. Its geodesic
  tetrahedra are the intersections of $H^3$ with the simplicial cones spanned by four linearly
  independent points of $H^3$, so all polyhedra are compact (no ideal vertices, as in Jessen's
  question); the isometry group is $O^+(1,3)$, the group of linear maps preserving the Minkowski
  form and the sheet $H^3$.

In both models a *polyhedron* is a finite union of geodesic tetrahedra with pairwise disjoint
interiors, and the *Dehn invariant* of a polyhedron is the sum over all edges $e$ of
$\ell(e) \otimes \theta(e)$, where $\ell(e)$ is the length of the edge and $\theta(e)$ its interior
dihedral angle, taken modulo rational multiples of $\pi$. Dehn's argument shows that this sum does
not depend on the chosen decomposition into tetrahedra and is invariant under scissors
congruence. In the hyperbolic case the Dehn invariant lives in
$\mathbb{R} \otimes_{\mathbb{Z}} \mathbb{R}/\mathbb{Q}\pi$. In the spherical case edge lengths are
themselves angles and, following Dupont and Sah, the Dehn invariant lives in
$\mathbb{R}/\mathbb{Q}\pi \otimes_{\mathbb{Z}} \mathbb{R}/\mathbb{Q}\pi$. (Taking the quotients by
$\mathbb{Z}\pi$ instead of $\mathbb{Q}\pi$, or the tensor product over $\mathbb{Q}$, gives
canonically isomorphic groups.)

*References:*
- [Wikipedia, Hilbert's third problem, Further information](https://en.wikipedia.org/wiki/Hilbert%27s_third_problem%23Further_information)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Je72] Jessen, B., _Zur Algebra der Polytope_, Nachr. Akad. Wiss. Göttingen Math.-Phys. Kl. II
  (1972), 47–53.
- [DS82] Dupont, J. L. and Sah, C. H., _Scissors congruences. II_, J. Pure Appl. Algebra 25
  (1982), 159–195. https://doi.org/10.1016/0022-4049(82)90035-4
- [Du01] Dupont, J. L., _Scissors congruences, group homology and characteristic classes_,
  Nankai Tracts in Mathematics 1, World Scientific (2001). https://doi.org/10.1142/9789812810335
-/

open MeasureTheory
open scoped ENNReal TensorProduct Pointwise Real

noncomputable section

namespace HilbertsThirdProblemForNonEuclideanGeometries

/-- The additive subgroup $\mathbb{Q}\pi$ of $\mathbb{R}$, as a $\mathbb{Q}$-submodule.
Angles in a Dehn invariant are taken modulo this subgroup, in `ℝ ⧸ ratPi`. -/
abbrev ratPi : Submodule ℚ ℝ := Submodule.span ℚ {π}

section Cone

variable {V : Type*} [AddCommMonoid V] [Module ℝ V]

/-- The closed simplicial cone $\{\sum_i c_i v_i \mid c_i \ge 0\}$ spanned by four vectors. -/
def simplicialCone (v : Fin 4 → V) : Set V :=
  {x | ∃ c : Fin 4 → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i}

/-- The open simplicial cone $\{\sum_i c_i v_i \mid c_i > 0\}$ spanned by four vectors. -/
def openSimplicialCone (v : Fin 4 → V) : Set V :=
  {x | ∃ c : Fin 4 → ℝ, (∀ i, 0 < c i) ∧ x = ∑ i, c i • v i}

end Cone

/- ### Spherical geometry -/

namespace Spherical

local notation "E" => EuclideanSpace ℝ (Fin 4)

/-- A (non-degenerate) geodesic tetrahedron in the unit sphere $S^3 \subseteq \mathbb{R}^4$, given
by four linearly independent unit vectors, its vertices. -/
structure Simplex where
  /-- The vertices of the tetrahedron. -/
  vertex : Fin 4 → E
  norm_vertex : ∀ i, ‖vertex i‖ = 1
  linearIndependent : LinearIndependent ℝ vertex

namespace Simplex

/-- The tetrahedron itself: the set of unit vectors in the simplicial cone spanned by the
vertices, i.e. the geodesic convex hull of the vertices in $S^3$. -/
def toSet (Δ : Simplex) : Set E :=
  Metric.sphere 0 1 ∩ simplicialCone Δ.vertex

/-- The interior of the tetrahedron relative to $S^3$: the set of unit vectors in the open
simplicial cone spanned by the vertices. -/
def interior (Δ : Simplex) : Set E :=
  Metric.sphere 0 1 ∩ openSimplicialCone Δ.vertex

end Simplex

/-- The spherical volume of a subset `P` of $S^3$: the surface measure of the unit sphere of
$\mathbb{R}^4$, given by `MeasureTheory.Measure.toSphere`, applied to `P`. -/
def volume (P : Set E) : ℝ≥0∞ :=
  (MeasureTheory.volume : Measure E).toSphere (Subtype.val ⁻¹' P)

/-- The interior dihedral angle of the tetrahedron with vertices `v` at the edge joining
`v i` and `v j`, where `k` and `l` are the two remaining vertices: the angle between the two
faces containing the edge, measured in the plane orthogonal to `v i` and `v j` (the normal plane
of the edge), as the angle between the orthogonal projections of `v k` and `v l` onto that
plane. -/
def dihedralAngle (v : Fin 4 → E) (i j k l : Fin 4) : ℝ :=
  InnerProductGeometry.angle
    ((Submodule.span ℝ {v i, v j})ᗮ.starProjection (v k))
    ((Submodule.span ℝ {v i, v j})ᗮ.starProjection (v l))

/-- The contribution $\ell \otimes \theta$ of the edge joining `v i` and `v j` to the spherical
Dehn invariant, where `k` and `l` are the two remaining vertices. The edge length
$\ell = \arccos \langle v_i, v_j\rangle$ is the spherical distance between the endpoints; both
$\ell$ and the dihedral angle $\theta$ are taken modulo $\mathbb{Q}\pi$. -/
def edgeTerm (v : Fin 4 → E) (i j k l : Fin 4) : (ℝ ⧸ ratPi) ⊗[ℤ] (ℝ ⧸ ratPi) :=
  Submodule.Quotient.mk (InnerProductGeometry.angle (v i) (v j)) ⊗ₜ[ℤ]
    Submodule.Quotient.mk (dihedralAngle v i j k l)

/-- The spherical Dehn invariant of a geodesic tetrahedron: the sum of $\ell(e) \otimes \theta(e)$
over its six edges, in $\mathbb{R}/\mathbb{Q}\pi \otimes_{\mathbb{Z}} \mathbb{R}/\mathbb{Q}\pi$. -/
def Simplex.dehnInvariant (Δ : Simplex) : (ℝ ⧸ ratPi) ⊗[ℤ] (ℝ ⧸ ratPi) :=
  edgeTerm Δ.vertex 0 1 2 3 + edgeTerm Δ.vertex 0 2 1 3 + edgeTerm Δ.vertex 0 3 1 2 +
    edgeTerm Δ.vertex 1 2 0 3 + edgeTerm Δ.vertex 1 3 0 2 + edgeTerm Δ.vertex 2 3 0 1

/-- The orthant $\{x \in S^3 \mid x_0, x_1, x_2, x_3 \ge 0\}$: the spherical tetrahedron whose
vertices are the standard basis vectors of $\mathbb{R}^4$. -/
def orthant : Simplex where
  vertex := EuclideanSpace.basisFun (Fin 4) ℝ
  norm_vertex i := by simp
  linearIndependent := (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.linearIndependent

/-- A spherical polyhedron, given by a decomposition into finitely many geodesic tetrahedra with
pairwise disjoint interiors. Every finite union of geodesic tetrahedra admits such a
decomposition. -/
structure Polyhedron where
  /-- The number of tetrahedra in the decomposition. -/
  n : ℕ
  /-- The tetrahedra of the decomposition. -/
  piece : Fin n → Simplex
  disjoint : Pairwise fun i j => Disjoint (piece i).interior (piece j).interior

namespace Polyhedron

/-- The polyhedron itself, as a subset of $S^3$. -/
def toSet (P : Polyhedron) : Set E :=
  ⋃ i, (P.piece i).toSet

/-- The spherical Dehn invariant of a polyhedron: the sum of the Dehn invariants of the tetrahedra
of its decomposition. By Dehn's argument this does not depend on the decomposition. -/
def dehnInvariant (P : Polyhedron) : (ℝ ⧸ ratPi) ⊗[ℤ] (ℝ ⧸ ratPi) :=
  ∑ i, (P.piece i).dehnInvariant

end Polyhedron

/-- Two subsets `P` and `Q` of $S^3$ are scissors-congruent if `P` can be cut into finitely many
geodesic tetrahedra with pairwise disjoint interiors which, after moving each of them by an
isometry of $S^3$ (an element of $O(4)$), have pairwise disjoint interiors and union `Q`. -/
def ScissorsCongruent (P Q : Set E) : Prop :=
  ∃ (n : ℕ) (S : Fin n → Simplex) (g : Fin n → E ≃ₗᵢ[ℝ] E),
    Pairwise (fun i j => Disjoint (S i).interior (S j).interior) ∧
    Pairwise (fun i j => Disjoint (g i '' (S i).interior) (g j '' (S j).interior)) ∧
    P = ⋃ i, (S i).toSet ∧ Q = ⋃ i, g i '' (S i).toSet

end Spherical

/- ### Hyperbolic geometry -/

namespace Hyperbolic

local notation "V" => Fin 4 → ℝ

/-- The Minkowski form $\langle x, y\rangle = x_0 y_0 - x_1 y_1 - x_2 y_2 - x_3 y_3$ on
$\mathbb{R}^4$. -/
def minkowski (x y : V) : ℝ :=
  x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3

/-- Hyperbolic $3$-space in the hyperboloid model: the upper sheet
$H^3 = \{x \mid \langle x, x\rangle = 1, x_0 > 0\}$ of the two-sheeted hyperboloid. -/
def hyperboloid : Set V :=
  {x | minkowski x x = 1 ∧ 0 < x 0}

/-- The hyperbolic distance $\operatorname{arcosh} \langle x, y\rangle$ between two points of
$H^3$. -/
def hyperbolicDist (x y : V) : ℝ :=
  Real.arcosh (minkowski x y)

/-- A (non-degenerate, compact) geodesic tetrahedron in $H^3$, given by four linearly independent
points of $H^3$, its vertices. -/
structure Simplex where
  /-- The vertices of the tetrahedron. -/
  vertex : Fin 4 → V
  vertex_mem : ∀ i, vertex i ∈ hyperboloid
  linearIndependent : LinearIndependent ℝ vertex

namespace Simplex

/-- The tetrahedron itself: the set of points of $H^3$ in the simplicial cone spanned by the
vertices, i.e. the geodesic convex hull of the vertices in $H^3$. -/
def toSet (Δ : Simplex) : Set V :=
  hyperboloid ∩ simplicialCone Δ.vertex

/-- The interior of the tetrahedron relative to $H^3$: the set of points of $H^3$ in the open
simplicial cone spanned by the vertices. -/
def interior (Δ : Simplex) : Set V :=
  hyperboloid ∩ openSimplicialCone Δ.vertex

end Simplex

/-- The hyperbolic volume of a subset `P` of $H^3$: four times the Lebesgue measure of the cone
$\{r x \mid 0 < r < 1, x \in P\}$ over `P`. Lebesgue measure on $\mathbb{R}^4$ is invariant under
$O^+(1,3)$ and decomposes as $r^3 \, dr \, d\mathrm{vol}_{H^3}$ in the polar coordinates
$x = r u$ ($u \in H^3$, $r > 0$), so this is the Riemannian volume of `P` in $H^3$. This is the
hyperboloid analogue of `MeasureTheory.Measure.toSphere`. -/
def volume (P : Set V) : ℝ≥0∞ :=
  4 * MeasureTheory.volume (Set.Ioo (0 : ℝ) 1 • P)

/-- The component of `x` Minkowski-orthogonal to the plane spanned by `u` and `w`, assuming the
restriction of the Minkowski form to that plane is non-degenerate: `x` minus its
Minkowski-orthogonal projection onto the plane, computed from the normal equations. -/
def normalComponent (u w x : V) : V :=
  x - ((minkowski w w * minkowski x u - minkowski u w * minkowski x w) /
        (minkowski u u * minkowski w w - minkowski u w ^ 2)) • u
    - ((minkowski u u * minkowski x w - minkowski u w * minkowski x u) /
        (minkowski u u * minkowski w w - minkowski u w ^ 2)) • w

/-- The angle between two spacelike vectors `p` and `q`, measured with the positive definite form
$-\langle \cdot, \cdot\rangle$ (the Riemannian metric of $H^3$ on tangent vectors). -/
def spacelikeAngle (p q : V) : ℝ :=
  Real.arccos (-minkowski p q / (√(-minkowski p p) * √(-minkowski q q)))

/-- The interior dihedral angle of the tetrahedron with vertices `v` at the edge joining
`v i` and `v j`, where `k` and `l` are the two remaining vertices: the angle between the two
faces containing the edge, measured in the (spacelike) Minkowski-orthogonal complement of the
plane spanned by `v i` and `v j` (the normal plane of the edge), as the angle between the
Minkowski-orthogonal components of `v k` and `v l` with respect to that plane. -/
def dihedralAngle (v : Fin 4 → V) (i j k l : Fin 4) : ℝ :=
  spacelikeAngle (normalComponent (v i) (v j) (v k)) (normalComponent (v i) (v j) (v l))

/-- The vertices of the trirectangular tetrahedron with apex $(1, 0, 0, 0)$ and three legs of
hyperbolic length `a` along the coordinate axes, used to test the definitions. -/
def trirectangularVertex (a : ℝ) : Fin 4 → V :=
  ![![1, 0, 0, 0], ![Real.cosh a, Real.sinh a, 0, 0], ![Real.cosh a, 0, Real.sinh a, 0],
    ![Real.cosh a, 0, 0, Real.sinh a]]

/-- The contribution $\ell \otimes \theta$ of the edge joining `v i` and `v j` to the hyperbolic
Dehn invariant, where `k` and `l` are the two remaining vertices: the hyperbolic length $\ell$ of
the edge tensored with its dihedral angle $\theta$ taken modulo $\mathbb{Q}\pi$. -/
def edgeTerm (v : Fin 4 → V) (i j k l : Fin 4) : ℝ ⊗[ℤ] (ℝ ⧸ ratPi) :=
  hyperbolicDist (v i) (v j) ⊗ₜ[ℤ] Submodule.Quotient.mk (dihedralAngle v i j k l)

/-- The hyperbolic Dehn invariant of a geodesic tetrahedron: the sum of
$\ell(e) \otimes \theta(e)$ over its six edges, in
$\mathbb{R} \otimes_{\mathbb{Z}} \mathbb{R}/\mathbb{Q}\pi$. -/
def Simplex.dehnInvariant (Δ : Simplex) : ℝ ⊗[ℤ] (ℝ ⧸ ratPi) :=
  edgeTerm Δ.vertex 0 1 2 3 + edgeTerm Δ.vertex 0 2 1 3 + edgeTerm Δ.vertex 0 3 1 2 +
    edgeTerm Δ.vertex 1 2 0 3 + edgeTerm Δ.vertex 1 3 0 2 + edgeTerm Δ.vertex 2 3 0 1

/-- A compact hyperbolic polyhedron, given by a decomposition into finitely many geodesic
tetrahedra with pairwise disjoint interiors. Every finite union of geodesic tetrahedra admits
such a decomposition. -/
structure Polyhedron where
  /-- The number of tetrahedra in the decomposition. -/
  n : ℕ
  /-- The tetrahedra of the decomposition. -/
  piece : Fin n → Simplex
  disjoint : Pairwise fun i j => Disjoint (piece i).interior (piece j).interior

namespace Polyhedron

/-- The polyhedron itself, as a subset of $H^3$. -/
def toSet (P : Polyhedron) : Set V :=
  ⋃ i, (P.piece i).toSet

/-- The hyperbolic Dehn invariant of a polyhedron: the sum of the Dehn invariants of the
tetrahedra of its decomposition. By Dehn's argument this does not depend on the decomposition. -/
def dehnInvariant (P : Polyhedron) : ℝ ⊗[ℤ] (ℝ ⧸ ratPi) :=
  ∑ i, (P.piece i).dehnInvariant

end Polyhedron

/-- A linear automorphism of $\mathbb{R}^4$ is an isometry of $H^3$ if it preserves the Minkowski
form and maps $H^3$ to itself. These are exactly the elements of $O^+(1,3)$, and their
restrictions to $H^3$ are exactly the isometries of hyperbolic $3$-space. -/
def IsIsometry (g : V ≃ₗ[ℝ] V) : Prop :=
  (∀ x y, minkowski (g x) (g y) = minkowski x y) ∧ Set.MapsTo g hyperboloid hyperboloid

/-- Two subsets `P` and `Q` of $H^3$ are scissors-congruent if `P` can be cut into finitely many
geodesic tetrahedra with pairwise disjoint interiors which, after moving each of them by an
isometry of $H^3$, have pairwise disjoint interiors and union `Q`. -/
def ScissorsCongruent (P Q : Set V) : Prop :=
  ∃ (n : ℕ) (S : Fin n → Simplex) (g : Fin n → V ≃ₗ[ℝ] V),
    (∀ i, IsIsometry (g i)) ∧
    Pairwise (fun i j => Disjoint (S i).interior (S j).interior) ∧
    Pairwise (fun i j => Disjoint (g i '' (S i).interior) (g j '' (S j).interior)) ∧
    P = ⋃ i, (S i).toSet ∧ Q = ⋃ i, g i '' (S i).toSet

end Hyperbolic

/-- **Hilbert's third problem for spherical geometry** (Jessen's question in $S^3$).
In spherical geometry, must polyhedra with the same volume and the same Dehn invariant be
scissors-congruent? That is, is it true that any two polyhedra $P, Q \subseteq S^3$ with
$\operatorname{vol}(P) = \operatorname{vol}(Q)$ and $D(P) = D(Q)$ in
$\mathbb{R}/\mathbb{Q}\pi \otimes_{\mathbb{Z}} \mathbb{R}/\mathbb{Q}\pi$ are scissors-congruent?
The converse (scissors-congruent polyhedra have the same volume and Dehn invariant) is known. -/
theorem hilberts_third_problem_for_non_euclidean_geometries.parts.i :
    ∀ P Q : Spherical.Polyhedron,
      Spherical.volume P.toSet = Spherical.volume Q.toSet →
      P.dehnInvariant = Q.dehnInvariant →
      Spherical.ScissorsCongruent P.toSet Q.toSet := by
  sorry

end HilbertsThirdProblemForNonEuclideanGeometries

end

theorem HilbertsThirdProblemForNonEuclideanGeometries.hilberts_third_problem_for_non_euclidean_geometries.parts.i.disproof : ¬ (type_of% @HilbertsThirdProblemForNonEuclideanGeometries.hilberts_third_problem_for_non_euclidean_geometries.parts.i) := sorry
