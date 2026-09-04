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
# Chern's conjecture for hypersurfaces in spheres

Chern's conjecture for hypersurfaces in spheres is a family of closely related conjectures
about closed minimal submanifolds (mostly hypersurfaces) of the unit sphere, going back to a
question of Chern (1968, 1970) and to Yau's 1982 problem list.

Throughout, $M^n$ is a closed (compact, connected, boundaryless) smooth $n$-manifold together
with a smooth immersion $f \colon M \to \mathbb{R}^{N}$ whose image lies in the unit sphere
$\mathbb{S}^{N-1}$. Mathlib has no theory of second fundamental forms or curvature of
submanifolds, so the required quantities are defined here concretely in the preferred chart
`extChartAt (𝓡 n) p` of `M` at `p`:
* the induced metric is the Gram matrix $g_{ij} = \langle \partial_i f, \partial_j f\rangle$ of
  the coordinate vector fields;
* the (vector valued) second fundamental form of $M$ in the sphere is the component
  $\mathrm{II}_{ij}$ of the second derivative $\partial_i\partial_j f$ orthogonal to both the
  tangent space and the position vector $f(p)$ (the unit normal of the sphere);
* $S = \sigma = \|\mathrm{II}\|^2 = g^{ik} g^{jl} \langle \mathrm{II}_{ij}, \mathrm{II}_{kl}\rangle$
  is the squared length of the second fundamental form, $\vec H = g^{ij}\mathrm{II}_{ij}$ is the
  mean curvature vector and $M$ is *minimal* when $\vec H \equiv 0$;
* for a unit normal $\nu$, the shape operator is
  $A^\nu = (g_{ij})^{-1} (\langle \mathrm{II}_{ij}, \nu\rangle)$, whose eigenvalues are the
  principal curvatures in direction $\nu$; a hypersurface is *isoparametric* when its principal
  curvatures are constant, and it is *of type $g$* when exactly $g$ of them are distinct;
* Lu's *fundamental matrix* is the Gram matrix $(\langle A^\alpha, A^\beta\rangle) =
  (\operatorname{tr}(A^\alpha A^\beta))$ of the shape operators with respect to an orthonormal
  frame of the normal space, and $\lambda_2$ is its second largest eigenvalue.

For a minimal hypersurface of the unit sphere the Gauss equation gives the scalar curvature
$k = n(n-1) - S$, so "constant scalar curvature" is the same as "constant $S$", and the set of
values of $k$ is discrete if and only if the set of values of $S$ is.

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Chern%27s_conjecture_for_hypersurfaces_in_spheres)
* S. S. Chern, *Minimal submanifolds in a Riemannian manifold*, Univ. of Kansas, 1968.
* S. T. Yau, *Problem section*, Seminar on Differential Geometry, Ann. Math. Stud. 102, 1982.
* Z. Lu, *Normal scalar curvature conjecture and its applications*, J. Funct. Anal. 261 (2011),
  [arXiv:0803.0502](https://arxiv.org/abs/0803.0502).
* L. Lei, H. W. Xu, Z. Y. Xu, *On Chern's conjecture for minimal hypersurfaces in spheres*,
  [arXiv:1712.01175](https://arxiv.org/abs/1712.01175).
-/

open scoped Manifold ContDiff EuclideanGeometry RealInnerProductSpace
open Matrix Module

namespace ChernsConjectureForHypersurfacesInSpheres

noncomputable section

variable (n : ℕ) {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ^n) M]

/- ### Smooth immersions into the unit sphere -/

/-- `f : M → ℝ^N` is a smooth immersion of the `n`-manifold `M` into the unit sphere
$\mathbb{S}^{N-1} \subseteq \mathbb{R}^N$. -/
structure IsImmersedInSphere (f : M → ℝ^N) : Prop where
  contMDiff : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ^N) ∞ f
  norm_eq_one : ∀ p, ‖f p‖ = 1
  injective_mfderiv : ∀ p, Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, ℝ^N) f p)

/-- The map `f` written in the preferred chart of `M` at `p`. -/
def localRep (f : M → ℝ^N) (p : M) : ℝ^n → ℝ^N :=
  f ∘ (extChartAt (𝓡 n) p).symm

/-- The first derivative of `f` at `p`, in the preferred chart of `M` at `p`. -/
def chartDeriv (f : M → ℝ^N) (p : M) : ℝ^n →L[ℝ] ℝ^N :=
  fderiv ℝ (localRep n f p) (extChartAt (𝓡 n) p p)

/-- The second derivative of `f` at `p`, in the preferred chart of `M` at `p`. -/
def chartDeriv₂ (f : M → ℝ^N) (p : M) : ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ^N :=
  fderiv ℝ (fderiv ℝ (localRep n f p)) (extChartAt (𝓡 n) p p)

/- ### Induced metric, second fundamental form, mean curvature -/

/-- The induced metric at `p` in the preferred chart: the Gram matrix
$g_{ij} = \langle \partial_i f, \partial_j f \rangle$ of the coordinate vector fields. -/
def metricMatrix (f : M → ℝ^N) (p : M) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    ⟪chartDeriv n f p (EuclideanSpace.single i 1), chartDeriv n f p (EuclideanSpace.single j 1)⟫

/-- The normal space of `f` at `p` inside the sphere: the orthogonal complement in `ℝ^N` of the
tangent space $df_p(T_pM)$ and of the position vector $f(p)$. -/
def normalSpace (f : M → ℝ^N) (p : M) : Submodule ℝ (ℝ^N) :=
  (LinearMap.range (chartDeriv n f p).toLinearMap ⊔ ℝ ∙ f p)ᗮ

/-- `ν` is a unit normal vector to `f` at `p`, tangent to the sphere. -/
def IsUnitNormal (f : M → ℝ^N) (p : M) (ν : ℝ^N) : Prop :=
  ν ∈ normalSpace n f p ∧ ‖ν‖ = 1

/-- The component $\mathrm{II}_{ij}$ of the vector valued second fundamental form of `f` (as a
submanifold of the sphere) at `p` in the preferred chart: the projection of the second derivative
$\partial_i \partial_j f$ onto the normal space. -/
def secondFundamentalForm (f : M → ℝ^N) (p : M) (i j : Fin n) : ℝ^N :=
  (normalSpace n f p).starProjection
    (chartDeriv₂ n f p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))

/-- The squared length $S = \sigma = \|\mathrm{II}\|^2 =
g^{ik} g^{jl} \langle \mathrm{II}_{ij}, \mathrm{II}_{kl}\rangle$ of the second fundamental form
of `f` at `p`. -/
def sffNormSq (f : M → ℝ^N) (p : M) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, (metricMatrix n f p)⁻¹ i k * (metricMatrix n f p)⁻¹ j l *
    ⟪secondFundamentalForm n f p i j, secondFundamentalForm n f p k l⟫

/-- The (unnormalised) mean curvature vector $\vec H = g^{ij} \mathrm{II}_{ij}$ of `f` at `p`. -/
def meanCurvatureVector (f : M → ℝ^N) (p : M) : ℝ^N :=
  ∑ i, ∑ j, (metricMatrix n f p)⁻¹ i j • secondFundamentalForm n f p i j

/-- `f` is a minimal immersion: its mean curvature vector vanishes identically. -/
def IsMinimal (f : M → ℝ^N) : Prop :=
  ∀ p, meanCurvatureVector n f p = 0

/- ### Shape operators, principal curvatures, isoparametric hypersurfaces -/

/-- The matrix $A^\nu = g^{-1} (\langle \mathrm{II}_{ij}, \nu \rangle)_{ij}$ of the shape operator
of `f` at `p` in direction `ν`, in the preferred chart. Its eigenvalues are the principal
curvatures of `f` at `p` in direction `ν`. -/
def shapeOperator (f : M → ℝ^N) (p : M) (ν : ℝ^N) : Matrix (Fin n) (Fin n) ℝ :=
  (metricMatrix n f p)⁻¹ * Matrix.of fun i j => ⟪secondFundamentalForm n f p i j, ν⟫

/-- A hypersurface `f` of the sphere is *isoparametric of type `g`* if it has constant principal
curvatures, `g` of which are distinct: there is a single polynomial `P` with exactly `g` distinct
roots such that, at every point, the characteristic polynomial of the shape operator with respect
to a suitable unit normal is `P`. (A unit normal is only determined up to sign, and the sign is
chosen pointwise; for a connected hypersurface this is equivalent to the principal curvatures being
locally constant with respect to any local unit normal field.) -/
def IsIsoparametricOfType (f : M → ℝ^N) (g : ℕ) : Prop :=
  ∃ P : Polynomial ℝ, P.roots.toFinset.card = g ∧
    ∀ p, ∃ ν, IsUnitNormal n f p ν ∧ (shapeOperator n f p ν).charpoly = P

/-- A hypersurface `f` of the sphere is *isoparametric* if it has constant principal
curvatures. -/
def IsIsoparametric (f : M → ℝ^N) : Prop :=
  ∃ g, IsIsoparametricOfType n f g

/- ### Lu's fundamental matrix -/

/-- Lu's *fundamental matrix* of `f` at `p`: the matrix
$(\langle A^\alpha, A^\beta \rangle) = (\operatorname{tr}(A^\alpha A^\beta))$ of inner products
of the shape operators $A^\alpha$ in the directions of an orthonormal basis $(\nu_\alpha)$ of the
normal space. Its eigenvalues do not depend on the choice of orthonormal basis. -/
def fundamentalMatrix (f : M → ℝ^N) (p : M) :
    Matrix (Fin (finrank ℝ (normalSpace n f p))) (Fin (finrank ℝ (normalSpace n f p))) ℝ :=
  Matrix.of fun α β =>
    Matrix.trace (shapeOperator n f p (stdOrthonormalBasis ℝ (normalSpace n f p) α) *
      shapeOperator n f p (stdOrthonormalBasis ℝ (normalSpace n f p) β))

/-- The fundamental matrix is symmetric. -/
theorem fundamentalMatrix_isHermitian (f : M → ℝ^N) (p : M) :
    (fundamentalMatrix n f p).IsHermitian := by
  refine Matrix.IsHermitian.ext fun α β => ?_
  simp only [fundamentalMatrix, Matrix.of_apply, star_trivial]
  exact Matrix.trace_mul_comm _ _

/-- The second largest eigenvalue $\lambda_2$ of the fundamental matrix of `f` at `p`
(eigenvalues are counted with multiplicity). In codimension `m = 1` the fundamental matrix is
`1 × 1`, there is no second eigenvalue, and $\lambda_2 = 0$ by convention. -/
def lambda₂ (f : M → ℝ^N) (p : M) : ℝ :=
  if h : 1 < finrank ℝ (normalSpace n f p) then
    (fundamentalMatrix_isHermitian n f p).eigenvalues₀ ⟨1, by simpa using h⟩
  else 0

/- ### Sets of values of the squared length of the second fundamental form -/

/-- The set $\mathcal{A}_{n,m}$ of all values of $\sigma = S$ taken on closed minimal
submanifolds $M^n$ immersed in the unit sphere $\mathbb{S}^{n+m}$ whose second fundamental form
has constant length. Connectedness (which includes nonemptiness) is part of "closed". -/
def submanifoldValues (n m : ℕ) : Set ℝ :=
  {σ | ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (ℝ^n) M),
    IsManifold (𝓡 n) ∞ M ∧ T2Space M ∧ CompactSpace M ∧ ConnectedSpace M ∧
    ∃ f : M → ℝ^(n + m + 1), IsImmersedInSphere n f ∧ IsMinimal n f ∧
      ∀ p, sffNormSq n f p = σ}

/-- The set of all values of $S$ (equivalently, by the Gauss equation $k = n(n-1) - S$, of the
scalar curvature $k$) taken on closed minimal hypersurfaces $M^n$ immersed in the unit sphere
$\mathbb{S}^{n+1}$ with constant scalar curvature. -/
def hypersurfaceValues (n : ℕ) : Set ℝ :=
  {S | ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (ℝ^n) M),
    IsManifold (𝓡 n) ∞ M ∧ T2Space M ∧ CompactSpace M ∧ ConnectedSpace M ∧
    ∃ f : M → ℝ^(n + 2), IsImmersedInSphere n f ∧ IsMinimal n f ∧
      ∀ p, sffNormSq n f p = S}

/- ### The conjectures -/

/-- **Chern's original question** (1968), in arbitrary codimension. Consider closed minimal
submanifolds $M^n$ immersed in the unit sphere $\mathbb{S}^{n+m}$ with second fundamental form of
constant length whose square is denoted by $\sigma$. Is the set $\mathcal{A}_{n,m}$ of values for
$\sigma$ discrete? Here the dimension $n$ and the codimension $m$ are both fixed. -/
theorem cherns_conjecture_for_hypersurfaces_in_spheres.variants.submanifolds :
    ∀ n m : ℕ, DiscreteTopology (submanifoldValues n m) := by
  sorry

/-- The Münzner values $a_k = (k - \operatorname{sgn}(5 - k))\, n$ for $k = 1, \dots, 5$, i.e.
$a_1 = 0$, $a_2 = n$, $a_3 = 2n$, $a_4 = 3n$, $a_5 = 5n$: the possible values of $S$ on a closed
isoparametric minimal hypersurface of $\mathbb{S}^{n+1}$. -/
def munznerValue (n k : ℕ) : ℝ :=
  ((k : ℝ) - (Int.sign (5 - (k : ℤ)) : ℝ)) * n

end

end ChernsConjectureForHypersurfacesInSpheres

theorem ChernsConjectureForHypersurfacesInSpheres.cherns_conjecture_for_hypersurfaces_in_spheres.variants.submanifolds.disproof : ¬ (type_of% @ChernsConjectureForHypersurfacesInSpheres.cherns_conjecture_for_hypersurfaces_in_spheres.variants.submanifolds) := sorry
