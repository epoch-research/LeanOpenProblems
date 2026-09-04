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
# Hopf conjecture

The Hopf conjectures relate the sign of the sectional curvature of a compact even-dimensional
Riemannian manifold to the sign of its Euler characteristic:

- A compact, even-dimensional Riemannian manifold with positive sectional curvature has positive
  Euler characteristic.
- A compact, $2d$-dimensional Riemannian manifold with negative sectional curvature has Euler
  characteristic of sign $(-1)^d$.

There are analogous conjectures when the curvature is allowed to vanish: non-negative sectional
curvature should give $\chi(M) \ge 0$, and non-positive sectional curvature should give
$(-1)^d \chi(M) \ge 0$.

For surfaces these statements follow from the Gauss–Bonnet theorem, and in dimension $4$ they
follow from Synge's theorem and Poincaré duality (or from the Chern–Gauss–Bonnet theorem). They
are open in dimension $6$ and higher.

Mathlib has Riemannian metrics (`Bundle.RiemannianBundle`, `IsContMDiffRiemannianBundle`) but
neither the Levi-Civita connection and its curvature, nor the Euler characteristic of a space.
This file therefore defines:

- `HopfConjecture.eulerCharacteristic`: the Euler characteristic
  $\sum_k (-1)^k \dim_{\mathbb{Q}} H_k(X; \mathbb{Q})$ of a topological space, via singular
  homology with rational coefficients;
- `HopfConjecture.sectionalCurvature`: the sectional curvature of a Riemannian manifold, computed
  in the chart at the base point from the Christoffel symbols of the Levi-Civita connection.

*References:*
- [Wikipedia, *Hopf conjecture*](https://en.wikipedia.org/wiki/Hopf_conjecture)
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- S.-T. Yau, *Problem section*, in: Seminar on Differential Geometry, Ann. of Math. Stud. 102,
  Princeton Univ. Press (1982), problems 8 and 10.
-/

open Bundle AlgebraicTopology ContinuousLinearMap
open scoped Manifold ContDiff

namespace HopfConjecture

universe u

/-
### Euler characteristic

The Euler characteristic of a topological space `X` is the alternating sum
$\chi(X) = \sum_k (-1)^k \dim_{\mathbb{Q}} H_k(X; \mathbb{Q})$ of its rational Betti numbers.
For a compact manifold only finitely many Betti numbers are non-zero and they are all finite,
so this is the usual Euler characteristic.
-/

/-- The `k`-th singular homology group of the topological space `X` with rational coefficients,
as a `ℚ`-module. -/
noncomputable abbrev rationalHomology (X : Type u) [TopologicalSpace X] (k : ℕ) :
    ModuleCat.{u} ℚ :=
  ((singularHomologyFunctor (ModuleCat.{u} ℚ) k).obj (ModuleCat.of ℚ (ULift.{u} ℚ))).obj
    (TopCat.of X)

/-- The Euler characteristic $\chi(X) = \sum_k (-1)^k \dim_{\mathbb{Q}} H_k(X; \mathbb{Q})$ of a
topological space `X`.

The sum is a `finsum`, so it is the usual Euler characteristic whenever only finitely many rational
Betti numbers are non-zero, which is the case for compact manifolds. -/
noncomputable def eulerCharacteristic (X : Type u) [TopologicalSpace X] : ℤ :=
  ∑ᶠ k : ℕ, (-1 : ℤ) ^ k * Module.finrank ℚ (rationalHomology X k)

/-- Every rational homology group of the empty space is zero. -/
@[category API, AMS 55]
theorem isZero_rationalHomology_of_isEmpty (X : Type u) [TopologicalSpace X] [IsEmpty X] (k : ℕ) :
    CategoryTheory.Limits.IsZero (rationalHomology X k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine CategoryTheory.Limits.IsZero.of_iso ?_
      (singularHomologyFunctorZeroOfTotallyDisconnectedSpace (ModuleCat.{u} ℚ)
        (ModuleCat.of ℚ (ULift.{u} ℚ)) (TopCat.of X))
    exact (CategoryTheory.Limits.isColimitEquivIsInitialOfIsEmpty _ _
      (CategoryTheory.Limits.colimit.isColimit _)).isZero
  · exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ _ _ _ hk.ne'

/-- The Euler characteristic of the empty space is `0`. This is why the strict Hopf conjectures
below assume that the manifold is nonempty. -/
@[category test, AMS 55]
theorem eulerCharacteristic_of_isEmpty (X : Type u) [TopologicalSpace X] [IsEmpty X] :
    eulerCharacteristic X = 0 := by
  unfold eulerCharacteristic
  have (k : ℕ) : Module.finrank ℚ (rationalHomology X k) = 0 := by
    have := ModuleCat.subsingleton_of_isZero (isZero_rationalHomology_of_isEmpty X k)
    exact Module.finrank_zero_of_subsingleton
  simp [this]

/-- The zeroth rational homology of a one-point space is one-dimensional. -/
@[category API, AMS 55]
theorem finrank_rationalHomology_zero_of_unique (X : Type u) [TopologicalSpace X] [Unique X] :
    Module.finrank ℚ (rationalHomology X 0) = 1 := by
  have e := singularHomologyFunctorZeroOfTotallyDisconnectedSpace (ModuleCat.{u} ℚ)
    (ModuleCat.of ℚ (ULift.{u} ℚ)) (TopCat.of X) ≪≫
    CategoryTheory.Limits.coproductUniqueIso
      (fun _ : TopCat.of X ↦ ModuleCat.of ℚ (ULift.{u} ℚ))
  rw [e.toLinearEquiv.finrank_eq]
  simp

/-- The Euler characteristic of a one-point space is `1`. -/
@[category test, AMS 55]
theorem eulerCharacteristic_of_unique (X : Type u) [TopologicalSpace X] [Unique X] :
    eulerCharacteristic X = 1 := by
  unfold eulerCharacteristic
  have h (k : ℕ) (hk : k ≠ 0) : Module.finrank ℚ (rationalHomology X k) = 0 := by
    have := ModuleCat.subsingleton_of_isZero
      (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat.{u} ℚ) k
        (ModuleCat.of ℚ (ULift.{u} ℚ)) (TopCat.of X) hk)
    exact Module.finrank_zero_of_subsingleton
  rw [finsum_eq_single _ 0 (fun k hk ↦ by simp [h k hk])]
  simp [finrank_rationalHomology_zero_of_unique]

/-
### Sectional curvature

Let `M` be a manifold modelled on `E` with a Riemannian metric on its tangent bundle. Around a
point `p : M`, we write the metric in the chart `extChartAt I p` as a family of bilinear forms
$g_y$ on `E`, indexed by points `y : E` of the chart target, and then use the classical
coordinate expressions
$$g_y(\Gamma_y(v, w), z) =
  \tfrac{1}{2} \left(\partial_v g(w, z) + \partial_w g(v, z) - \partial_z g(v, w)\right)(y)$$
for the Christoffel symbols of the Levi-Civita connection,
$$R_y(u, v) w = \partial_u \Gamma(v, w) - \partial_v \Gamma(u, w)
  + \Gamma_y(u, \Gamma_y(v, w)) - \Gamma_y(v, \Gamma_y(u, w))$$
for the Riemann curvature tensor $R(X, Y) Z = \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z
- \nabla_{[X, Y]} Z$, and
$$K(u, v) = \frac{g(R(u, v) v, u)}{g(u, u) g(v, v) - g(u, v)^2}$$
for the sectional curvature of the plane spanned by `u` and `v`.

These definitions are meant for boundaryless manifolds with a `C^∞` metric. With this convention
the round sphere has positive sectional curvature and hyperbolic space has negative sectional
curvature.
-/

section Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The Riemannian metric of `M` written in the chart at `p`: for `y` in the target of
`extChartAt I p`, this is the bilinear form on `E` obtained by pulling back the inner product on
the tangent space at `(extChartAt I p).symm y` along the trivialization of the tangent bundle
associated with the chart at `p`. In other words, `metricInChart I p y u v` is the value on the
coordinate vectors `u`, `v` of the metric coefficients at the chart coordinate `y`. -/
noncomputable def metricInChart (p : M) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ (E := TangentSpace I ((extChartAt I p).symm y))).bilinearComp
    ((trivializationAt E (TangentSpace I) p).symmL ℝ ((extChartAt I p).symm y))
    ((trivializationAt E (TangentSpace I) p).symmL ℝ ((extChartAt I p).symm y))

/-- At the base point of the chart, the coordinate expression of the metric is the inner product
on the tangent space. -/
@[category API, AMS 53]
theorem metricInChart_extChartAt_self (p : M) (u v : TangentSpace I p) :
    metricInChart I p (extChartAt I p p) u v = inner ℝ u v := by
  have h : ∀ w : E, (tangentBundleCore I M).coordChange (achart H p) (achart H p) p w = w :=
    fun w ↦ tangentCoordChange_self (mem_extChartAt_source p)
  rw [metricInChart, bilinearComp_apply, extChartAt_to_inv,
    TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source H p)]
  erw [h, h]
  rfl

/-- The Christoffel symbols of the Levi-Civita connection in the chart at `p`, packaged as a
bilinear map: `christoffel I p y v w` is the covariant derivative `∇ᵥ w` at the chart coordinate
`y` of the constant coordinate vector fields `v` and `w`. It is determined by the Koszul formula
`2 g(∇ᵥ w, z) = ∂ᵥ g(w, z) + ∂_w g(v, z) - ∂_z g(v, w)`, where `g` is the metric in the chart. -/
noncomputable def christoffel (p : M) (y : E) (v w : E) : E :=
  let dg := fderiv ℝ (metricInChart I p) y
  (metricInChart I p y).inverse ((1 / 2 : ℝ) • (dg v w + dg w v - (dg.flip v).flip w))

/-- The Riemann curvature tensor `R(u, v) w = ∇ᵤ ∇ᵥ w - ∇ᵥ ∇ᵤ w` of the constant coordinate vector
fields `u`, `v`, `w` in the chart at `p`, evaluated at the chart coordinate `y`. Here
`∇ᵤ X = ∂ᵤ X + Γ(u, X)` for a vector field `X` written in coordinates. -/
noncomputable def riemannCurvature (p : M) (y : E) (u v w : E) : E :=
  fderiv ℝ (fun z ↦ christoffel I p z v w) y u - fderiv ℝ (fun z ↦ christoffel I p z u w) y v +
    christoffel I p y u (christoffel I p y v w) - christoffel I p y v (christoffel I p y u w)

/-- The sectional curvature `K(u, v) = g(R(u, v) v, u) / (g(u, u) g(v, v) - g(u, v)²)` of the
plane spanned by two linearly independent tangent vectors `u`, `v` at `p`. It is computed in the
chart at `p`, where tangent vectors at `p` coincide with coordinate vectors. With this convention
the round sphere has positive sectional curvature. (Junk value `0` if `u`, `v` are linearly
dependent.) -/
noncomputable def sectionalCurvature (p : M) (u v : TangentSpace I p) : ℝ :=
  let y := extChartAt I p p
  let g := metricInChart I p y
  g (riemannCurvature I p y u v v) u / (g u u * g v v - g u v ^ 2)

end Curvature

section Flat

/-
The standard Riemannian metric of an inner product space `F` (see `riemannianMetricVectorSpace`)
is flat: its sectional curvature vanishes.
-/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- In an inner product space with its canonical Riemannian metric, the metric in the chart is
constant, equal to the inner product. -/
@[category test, AMS 53]
theorem metricInChart_model_space (p y : F) :
    metricInChart 𝓘(ℝ, F) p y = (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) := by
  ext u v
  simp only [metricInChart, bilinearComp_apply, TangentBundle.symmL_model_space]
  rfl

/-- The Christoffel symbols of an inner product space vanish. -/
@[category test, AMS 53]
theorem christoffel_model_space (p y v w : F) : christoffel 𝓘(ℝ, F) p y v w = 0 := by
  have h1 : metricInChart 𝓘(ℝ, F) p = fun _ ↦ (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) :=
    funext (metricInChart_model_space p)
  have h2 : fderiv ℝ (metricInChart 𝓘(ℝ, F) p) y = 0 := by
    rw [h1]
    exact fderiv_const_apply (𝕜 := ℝ) (E := F) (F := F →L[ℝ] F →L[ℝ] ℝ) (x := y) _
  unfold christoffel
  rw [h2]
  simp

/-- The Riemann curvature tensor of an inner product space vanishes. -/
@[category test, AMS 53]
theorem riemannCurvature_model_space (p y u v w : F) :
    riemannCurvature 𝓘(ℝ, F) p y u v w = 0 := by
  simp [riemannCurvature, christoffel_model_space]

/-- An inner product space is flat: its sectional curvature vanishes. -/
@[category test, AMS 53]
theorem sectionalCurvature_model_space (p : F) (u v : TangentSpace 𝓘(ℝ, F) p) :
    sectionalCurvature 𝓘(ℝ, F) p u v = 0 := by
  simp [sectionalCurvature, riemannCurvature_model_space]

end Flat

/-
### The conjectures

In the statements below, `M` is a closed (compact, without boundary) smooth manifold of dimension
`2 * d`, modelled on `EuclideanSpace ℝ (Fin (2 * d))` with the boundaryless model `𝓡 (2 * d)`,
equipped with a smooth Riemannian metric. Compactness together with the finite-dimensional charts
implies second countability, so `M` is a closed manifold in the usual sense. A sign condition on
the sectional curvature is required on every `2`-plane at every point, i.e. for every pair of
linearly independent tangent vectors. Connectedness is not assumed, since the Euler
characteristic is additive over connected components.
-/

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 * d))) M] [IsManifold (𝓡 (2 * d)) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 (2 * d)) x)]
  [IsContMDiffRiemannianBundle (𝓡 (2 * d)) ∞ (EuclideanSpace ℝ (Fin (2 * d)))
    (fun x : M ↦ TangentSpace (𝓡 (2 * d)) x)]

/-- **Hopf conjecture, positive curvature case** (problem 8 in Yau's list).
A compact, even-dimensional Riemannian manifold with positive sectional curvature has positive
Euler characteristic: if $M$ is a closed Riemannian manifold of dimension $2d$ whose sectional
curvature is positive on every $2$-plane at every point, then $\chi(M) > 0$.

The manifold is assumed nonempty: the empty manifold vacuously has positive sectional curvature
but Euler characteristic `0`. This is a theorem for $d = 1, 2$ and open for $d \ge 3$. -/
@[category research open, AMS 53 57]
theorem hopf_conjecture.parts.i [Nonempty M]
    (hK : ∀ (p : M) (u v : TangentSpace (𝓡 (2 * d)) p), LinearIndependent ℝ ![u, v] →
      0 < sectionalCurvature (𝓡 (2 * d)) p u v) :
    0 < eulerCharacteristic M := by
  sorry

/-- **Hopf conjecture, negative curvature case** (problem 10 in Yau's list).
A compact, $2d$-dimensional Riemannian manifold with negative sectional curvature has Euler
characteristic of sign $(-1)^d$: if $M$ is a closed Riemannian manifold of dimension $2d$ whose
sectional curvature is negative on every $2$-plane at every point, then $(-1)^d \chi(M) > 0$.

The manifold is assumed nonempty: the empty manifold vacuously has negative sectional curvature
but Euler characteristic `0`. This is a theorem for $d = 1, 2$ and open for $d \ge 3$. -/
@[category research open, AMS 53 57]
theorem hopf_conjecture.parts.ii [Nonempty M]
    (hK : ∀ (p : M) (u v : TangentSpace (𝓡 (2 * d)) p), LinearIndependent ℝ ![u, v] →
      sectionalCurvature (𝓡 (2 * d)) p u v < 0) :
    0 < (-1) ^ d * eulerCharacteristic M := by
  sorry

/-- **Hopf conjecture, non-negative curvature case** (Question 1 of Chern).
A compact, even-dimensional Riemannian manifold with non-negative sectional curvature has
non-negative Euler characteristic: if $M$ is a closed Riemannian manifold of dimension $2d$ whose
sectional curvature is non-negative on every $2$-plane at every point, then $\chi(M) \ge 0$. -/
@[category research open, AMS 53 57]
theorem hopf_conjecture.variants.nonneg_curvature
    (hK : ∀ (p : M) (u v : TangentSpace (𝓡 (2 * d)) p), LinearIndependent ℝ ![u, v] →
      0 ≤ sectionalCurvature (𝓡 (2 * d)) p u v) :
    0 ≤ eulerCharacteristic M := by
  sorry

/-- **Hopf conjecture, non-positive curvature case.**
A compact, $2d$-dimensional Riemannian manifold with non-positive sectional curvature has Euler
characteristic of sign $(-1)^d$ or zero: if $M$ is a closed Riemannian manifold of dimension $2d$
whose sectional curvature is non-positive on every $2$-plane at every point, then
$(-1)^d \chi(M) \ge 0$. -/
@[category research open, AMS 53 57]
theorem hopf_conjecture.variants.nonpos_curvature
    (hK : ∀ (p : M) (u v : TangentSpace (𝓡 (2 * d)) p), LinearIndependent ℝ ![u, v] →
      sectionalCurvature (𝓡 (2 * d)) p u v ≤ 0) :
    0 ≤ (-1) ^ d * eulerCharacteristic M := by
  sorry

end HopfConjecture
