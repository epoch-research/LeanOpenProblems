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
# Scissors congruence in spherical and hyperbolic geometry

In spherical or hyperbolic geometry, must polyhedra with the same volume and Dehn invariant be
scissors-congruent?

In Euclidean $3$-space, two polyhedra are scissors congruent (one can be cut into finitely many
polyhedral pieces that reassemble into the other) if and only if they have the same volume and
the same Dehn invariant (Dehn 1901, Sydler 1965). The Dehn invariant of a polyhedron is
$$\sum_{e} \ell(e) \otimes \theta(e)
  \in \mathbb{R} \otimes_{\mathbb{Z}} (\mathbb{R}/\pi\mathbb{Z}),$$
the sum over the edges $e$ of the length $\ell(e)$ tensored with the interior dihedral angle
$\theta(e)$. The analogous invariants make sense for polyhedra in the $3$-sphere $S^3$ and in
hyperbolic $3$-space $H^3$; equal volume and equal Dehn invariant are necessary for scissors
congruence there as well (Dupont–Sah), but whether they are sufficient is open in both geometries.

We model both spaces as quadrics in $\mathbb{R}^4$: the unit sphere
$S^3 = \{x : \langle x, x\rangle = 1\}$ and the upper sheet
$H^3 = \{x : \langle x, x\rangle_{1,3} = -1,\ x_0 > 0\}$ of the two-sheeted hyperboloid of the
Minkowski form $\langle x, y\rangle_{1,3} = -x_0 y_0 + x_1 y_1 + x_2 y_2 + x_3 y_3$. In both
models the totally geodesic surfaces are the intersections with linear hyperplanes of
$\mathbb{R}^4$, a geodesic simplex is the intersection of the model with the cone spanned by four
linearly independent points of the model, the ambient form restricts to the Riemannian metric on
each tangent space, and the Riemannian volume of a region $P$ equals $4$ times the Lebesgue
measure of the cone $\{t x : x \in P,\ 0 < t \le 1\}$.

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Spherical geometry](https://en.wikipedia.org/wiki/Spherical_geometry)
- [Wikipedia, Hyperbolic geometry](https://en.wikipedia.org/wiki/Hyperbolic_geometry)
- [Wikipedia, Dehn invariant](https://en.wikipedia.org/wiki/Dehn_invariant)
- [Wikipedia, Hilbert's third problem](https://en.wikipedia.org/wiki/Hilbert%27s_third_problem)
- J. L. Dupont, C. H. Sah, *Scissors congruences, II*, J. Pure Appl. Algebra 25 (1982), 159–195.
- J. L. Dupont, *Scissors congruences, group homology and characteristic classes*,
  Nankai Tracts in Mathematics 1, World Scientific, 2001.
-/

open Function MeasureTheory Real
open scoped TensorProduct

namespace Spherical

/-- The ambient space `ℝ⁴` of the quadric models of `S³` and `H³`. -/
local notation "ℝ⁴" => Fin 4 → ℝ

/--
The Riemannian volume of a subset `P` of the sphere `S³` or of the hyperboloid `H³` in `ℝ⁴`:
`4` times the Lebesgue measure of the cone $\{t x : x \in P,\ 0 < t \le 1\} \subseteq \mathbb{R}^4$.

In "polar coordinates" $y = t x$ with $x$ in the model, the Lebesgue measure of $\mathbb{R}^4$
is $t^3\,dt\,d\mathrm{vol}$, where $d\mathrm{vol}$ is the Riemannian volume of the model (for
both the sphere and the hyperboloid), and $\int_0^1 t^3\,dt = 1/4$.
-/
noncomputable def riemannianVolume (P : Set ℝ⁴) : ENNReal :=
  4 * volume {y | ∃ x ∈ P, ∃ t ∈ Set.Ioc (0 : ℝ) 1, y = t • x}

/--
A quadric model of a three-dimensional space form inside `ℝ⁴`. The data consists of

* a nondegenerate bilinear `form` on `ℝ⁴` (symmetric in both instances), whose restriction to
  the tangent space of the model at each point is the Riemannian metric;
* the set `points` of the model, a level set of `form` (for `H³` also cut down to one sheet);
* the geodesic distance `dist` between two points of the model, expressed through the form.

The two instances are `Spherical.sphere` (`S³`) and `Spherical.hyperbolic` (`H³`).
-/
structure Model where
  /-- The ambient bilinear form. -/
  form : LinearMap.BilinForm ℝ ℝ⁴
  /-- The ambient form is nondegenerate. -/
  form_nondegenerate : form.Nondegenerate
  /-- The points of the model. -/
  points : Set ℝ⁴
  /-- The geodesic distance between two points of the model. -/
  dist : ℝ⁴ → ℝ⁴ → ℝ

namespace Model

variable (M : Model)

/--
A nondegenerate geodesic simplex (tetrahedron) in the model `M`, given by its four vertices,
which are points of the model that are linearly independent in `ℝ⁴`.
-/
structure Simplex where
  /-- The four vertices of the simplex. -/
  vertex : Fin 4 → ℝ⁴
  /-- The vertices are points of the model. -/
  vertex_mem : ∀ i, vertex i ∈ M.points
  /-- The vertices are linearly independent in `ℝ⁴`. -/
  linearIndependent : LinearIndependent ℝ vertex

/--
A map `f` is an isometry of the model `M` if it maps the points of the model bijectively onto
themselves and preserves the geodesic distance.
-/
def IsIsometry (f : ℝ⁴ → ℝ⁴) : Prop :=
  Set.BijOn f M.points M.points ∧
    ∀ x ∈ M.points, ∀ y ∈ M.points, M.dist (f x) (f y) = M.dist x y

/-- Two subsets `A`, `B` of the model are congruent if an isometry of the model maps `A` onto `B`.
-/
def Congruent (A B : Set ℝ⁴) : Prop :=
  ∃ f, M.IsIsometry f ∧ f '' A = B

namespace Simplex

variable {M} (T : M.Simplex)

/--
The underlying set of a geodesic simplex: the points of the model lying in the cone spanned by
the four vertices. For `S³` this is the spherical tetrahedron with the given vertices (it lies in
an open hemisphere), and for `H³` it is the hyperbolic tetrahedron with the given vertices.
-/
def toSet : Set ℝ⁴ :=
  {x ∈ M.points | ∃ t : Fin 4 → ℝ, (∀ i, 0 ≤ t i) ∧ x = ∑ i, t i • T.vertex i}

/--
The interior of a geodesic simplex relative to the model: the points of the model lying in the
open cone spanned by the four vertices, i.e. the positive combinations of the vertices.
-/
def relInterior : Set ℝ⁴ :=
  {x ∈ M.points | ∃ t : Fin 4 → ℝ, (∀ i, 0 < t i) ∧ x = ∑ i, t i • T.vertex i}

/-- The vertices of a simplex form a basis of `ℝ⁴`. -/
noncomputable def basis : Module.Basis (Fin 4) ℝ ℝ⁴ :=
  basisOfLinearIndependentOfCardEqFinrank T.linearIndependent (by simp)

/--
The inward normal `T.innerNormal k` of the face of `T` opposite to the vertex `k`: the unique
vector `n` with `M.form n (T.vertex j) = if j = k then 1 else 0`. It is orthogonal to the three
vertices of that face, so it is tangent to the model along the face and normal to the face,
and it points to the side of the face containing the simplex, since the simplex is
$\{x : M.\mathrm{form}\,(n_k)\,x \ge 0 \text{ for all } k\}$ intersected with the model.
-/
noncomputable def innerNormal (k : Fin 4) : ℝ⁴ :=
  M.form.dualBasis M.form_nondegenerate T.basis k

/--
The interior dihedral angle of `T` along the edge shared by the faces opposite to the vertices
`k` and `l` (with `k ≠ l`), that is, the edge joining the two remaining vertices. It is the
angle in $[0, \pi]$ of the wedge $\{w : g(n_k, w) \ge 0,\ g(n_l, w) \ge 0\}$ in the tangent
space of the model at a point of the edge, where $g$ is the ambient form (a Euclidean inner
product on that tangent space) and $n_k$, $n_l$ are the inward normals:
$$\theta_{kl} = \arccos\left(\frac{-g(n_k, n_l)}{\sqrt{g(n_k, n_k)\, g(n_l, n_l)}}\right).$$
-/
noncomputable def dihedralAngle (k l : Fin 4) : ℝ :=
  arccos (-(M.form (T.innerNormal k) (T.innerNormal l)) /
    √(M.form (T.innerNormal k) (T.innerNormal k) * M.form (T.innerNormal l) (T.innerNormal l)))

/-- The length of the edge of `T` joining the vertices `i` and `j`. -/
noncomputable def edgeLength (i j : Fin 4) : ℝ :=
  M.dist (T.vertex i) (T.vertex j)

/--
The Dehn invariant of a geodesic simplex, an element of
$\mathbb{R} \otimes_{\mathbb{Z}} (\mathbb{R}/\pi\mathbb{Z})$: the sum over the six edges of the
edge length tensored with the interior dihedral angle along that edge. The edge joining the
vertices `i` and `j` is shared by the faces opposite to the two remaining vertices.
-/
noncomputable def dehnInvariant : ℝ ⊗[ℤ] AddCircle π :=
  T.edgeLength 0 1 ⊗ₜ[ℤ] (T.dihedralAngle 2 3 : AddCircle π) +
  T.edgeLength 0 2 ⊗ₜ[ℤ] (T.dihedralAngle 1 3 : AddCircle π) +
  T.edgeLength 0 3 ⊗ₜ[ℤ] (T.dihedralAngle 1 2 : AddCircle π) +
  T.edgeLength 1 2 ⊗ₜ[ℤ] (T.dihedralAngle 0 3 : AddCircle π) +
  T.edgeLength 1 3 ⊗ₜ[ℤ] (T.dihedralAngle 0 2 : AddCircle π) +
  T.edgeLength 2 3 ⊗ₜ[ℤ] (T.dihedralAngle 0 1 : AddCircle π)

end Simplex

/--
A family of geodesic simplices is a dissection of a set `P` if the simplices have pairwise
disjoint relative interiors and their union is `P`.
-/
def IsDissection {n : ℕ} (S : Fin n → M.Simplex) (P : Set ℝ⁴) : Prop :=
  Pairwise (Disjoint on fun i => (S i).relInterior) ∧ (⋃ i, (S i).toSet) = P

/--
A polyhedron in the model `M`: a finite union of geodesic simplices with pairwise disjoint
relative interiors. The dissection into simplices is part of the data, and it is used to
compute the Dehn invariant (which does not depend on the chosen dissection).
-/
structure Polyhedron where
  /-- The number of simplices. -/
  n : ℕ
  /-- The simplices. -/
  simplex : Fin n → M.Simplex
  /-- The simplices have pairwise disjoint relative interiors. -/
  disjoint : Pairwise (Disjoint on fun i => (simplex i).relInterior)

namespace Polyhedron

variable {M} (P : M.Polyhedron)

/-- The underlying set of a polyhedron. -/
def toSet : Set ℝ⁴ := ⋃ i, (P.simplex i).toSet

/-- The volume of a polyhedron. -/
noncomputable def volume : ENNReal := riemannianVolume P.toSet

/-- The Dehn invariant of a polyhedron: the sum of the Dehn invariants of its simplices. -/
noncomputable def dehnInvariant : ℝ ⊗[ℤ] AddCircle π := ∑ i, (P.simplex i).dehnInvariant

end Polyhedron

/--
Two subsets `P`, `Q` of the model are scissors congruent if they can be dissected into the same
finite number of geodesic simplices `S 0, …, S (n - 1)` and `T 0, …, T (n - 1)` such that
`S i` is congruent to `T i` for every `i`.
-/
def ScissorsCongruent (P Q : Set ℝ⁴) : Prop :=
  ∃ (n : ℕ) (S T : Fin n → M.Simplex), M.IsDissection S P ∧ M.IsDissection T Q ∧
    ∀ i, M.Congruent (S i).toSet (T i).toSet

end Model

/-- The standard inner product $\langle x, y\rangle = \sum_i x_i y_i$ on `ℝ⁴`. -/
noncomputable def sphericalForm : LinearMap.BilinForm ℝ ℝ⁴ := Matrix.toBilin' 1

/-- The Minkowski form $\langle x, y\rangle_{1,3} = -x_0 y_0 + x_1 y_1 + x_2 y_2 + x_3 y_3$
on `ℝ⁴`. -/
noncomputable def minkowskiForm : LinearMap.BilinForm ℝ ℝ⁴ :=
  Matrix.toBilin' (Matrix.diagonal ![-1, 1, 1, 1])

/-- Pairing with a standard basis vector picks out a coordinate. -/
theorem sphericalForm_single_right (x : ℝ⁴) (j : Fin 4) :
    sphericalForm x (Pi.single j 1) = x j := by
  simp only [sphericalForm, Matrix.toBilin'_apply', Matrix.one_mulVec, dotProduct_single_one]

/-- The standard basis of `ℝ⁴` is orthonormal for the standard inner product. -/
theorem sphericalForm_single_single (k l : Fin 4) :
    sphericalForm (Pi.single k 1) (Pi.single l 1) = if k = l then 1 else 0 := by
  rw [sphericalForm_single_right, Pi.single_apply]; simp [eq_comm]

/-- The standard inner product is nondegenerate. -/
theorem sphericalForm_nondegenerate : sphericalForm.Nondegenerate := by
  rw [sphericalForm, LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero]
  simp

/-- The Minkowski form is nondegenerate. -/
theorem minkowskiForm_nondegenerate : minkowskiForm.Nondegenerate := by
  rw [minkowskiForm, LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero,
    Matrix.det_diagonal]
  simp [Fin.prod_univ_four]

/--
The unit $3$-sphere $S^3 = \{x \in \mathbb{R}^4 : \langle x, x\rangle = 1\}$ with its round
metric: the geodesic distance between $x$ and $y$ is $\arccos\langle x, y\rangle$.
-/
noncomputable def sphere : Model where
  form := sphericalForm
  form_nondegenerate := sphericalForm_nondegenerate
  points := {x | sphericalForm x x = 1}
  dist x y := arccos (sphericalForm x y)

/--
Hyperbolic $3$-space in the hyperboloid model: the upper sheet
$H^3 = \{x \in \mathbb{R}^4 : \langle x, x\rangle_{1,3} = -1,\ x_0 > 0\}$ of the hyperboloid of
the Minkowski form, with geodesic distance $\operatorname{arcosh}(-\langle x, y\rangle_{1,3})$.
-/
noncomputable def hyperbolic : Model where
  form := minkowskiForm
  form_nondegenerate := minkowskiForm_nondegenerate
  points := {x | minkowskiForm x x = -1 ∧ 0 < x 0}
  dist x y := arcosh (-minkowskiForm x y)

/--
The spherical orthant tetrahedron, whose vertices are the standard basis vectors of `ℝ⁴`. It is
one of the sixteen cells into which the coordinate hyperplanes cut `S³`.
-/
noncomputable def orthant : sphere.Simplex where
  vertex i := Pi.single i 1
  vertex_mem i := by simp [sphere, sphericalForm_single_single]
  linearIndependent := by
    have h := (Pi.basisFun ℝ (Fin 4)).linearIndependent
    have e : ⇑(Pi.basisFun ℝ (Fin 4)) = fun i : Fin 4 => (Pi.single i 1 : ℝ⁴) := by
      ext i; simp
    rwa [e] at h

/--
**Spherical case.** Must two polyhedra in the $3$-sphere $S^3$ with the same volume and the same
Dehn invariant (in $\mathbb{R} \otimes_{\mathbb{Z}} (\mathbb{R}/\pi\mathbb{Z})$) be scissors
congruent? Here a polyhedron is a finite union of nondegenerate spherical tetrahedra with
pairwise disjoint interiors, and scissors congruence allows all isometries of $S^3$.
-/
theorem spherical.parts.i : 
    ∀ P Q : sphere.Polyhedron, P.volume = Q.volume → P.dehnInvariant = Q.dehnInvariant →
      sphere.ScissorsCongruent P.toSet Q.toSet := by
  sorry

end Spherical

theorem Spherical.spherical.parts.i.disproof : ¬ (type_of% @Spherical.spherical.parts.i) := sorry
