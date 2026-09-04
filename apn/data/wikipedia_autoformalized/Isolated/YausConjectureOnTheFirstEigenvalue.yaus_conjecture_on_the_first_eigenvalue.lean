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
# Yau's conjecture on the first eigenvalue

Yau's conjecture (1982) states that the first (nonzero) eigenvalue of the Laplace–Beltrami
operator on a closed embedded minimal hypersurface $M^n$ of the unit sphere $S^{n+1}$ is $n$.

Mathlib does not (yet) have the Laplace–Beltrami operator or the mean curvature of a Riemannian
submanifold. Since the hypersurfaces in question are submanifolds of the Euclidean space
$\mathbb{R}^{n+2}$, we define these notions extrinsically, from the ambient calculus:

* the tangent space of $M$ at $\iota(x)$ is the image of the differential of the embedding $\iota$;
* the gradient of a function on $M$ is the tangential projection of the ambient gradient, i.e.
  the unique tangent vector representing the differential of the function on the tangent space;
* the divergence of a tangent vector field $X$ along $M$ is the trace over the tangent space of
  $v \mapsto P(D_v X)$, where $P$ is the orthogonal projection onto the tangent space and
  $D_v X$ is the ambient derivative of $X$ along $M$ in the tangent direction $v$; this is the
  trace of the Levi-Civita covariant derivative of the induced metric;
* the Laplace–Beltrami operator is $\Delta f = \operatorname{div}(\nabla f)$;
* the mean curvature vector of $M$ in $\mathbb{R}^{n+2}$ is $\vec H = \Delta \iota$, the Laplacian
  of the position vector (equivalently, the trace of the second fundamental form);
* $M \subseteq S^{n+1}$ is minimal in $S^{n+1}$ if its mean curvature vector in $S^{n+1}$, which is
  the component of $\vec H$ tangent to the sphere, vanishes, i.e. $\vec H(p)$ is a multiple of $p$.

Derivatives along $M$ are taken with `fderivWithin` on the image of $\iota$; on tangent vectors
these are uniquely determined, and the definitions above depend only on their values on tangent
vectors.

*References:*
- [Wikipedia, Yau's conjecture on the first eigenvalue](https://en.wikipedia.org/wiki/Yau%27s_conjecture_on_the_first_eigenvalue)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- S.-T. Yau, *Seminar on Differential Geometry*, Annals of Mathematics Studies 102, Princeton
  University Press, 1982, Problem Section.
- Z. Tang, W. Yan, *Isoparametric foliation and Yau conjecture on the first eigenvalue*,
  J. Differential Geom. 94 (2013), 521–540, [arXiv:1201.0666](https://arxiv.org/abs/1201.0666).
-/

open scoped Manifold ContDiff
open Manifold

namespace YausConjectureOnTheFirstEigenvalue

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (ι : M → EuclideanSpace ℝ (Fin (n + 2)))

/-- The tangent space at `ι x` of the submanifold `Set.range ι` of `ℝ^{n+2}`, as a subspace of
the ambient Euclidean space: the image of the differential of `ι` at `x`. -/
noncomputable def ambientTangentSpace (x : M) : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 2))) :=
  LinearMap.range (mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 2))) ι x).toLinearMap

/-- The gradient at `ι x` of a function `f : M → ℝ` with respect to the metric induced by `ι`,
as a vector of the ambient space. It is the orthogonal projection onto the tangent space of the
ambient gradient of `f ∘ ι⁻¹` along `Set.range ι`: the unique tangent vector `v` at `ι x` such
that `⟪v, w⟫ = d(f ∘ ι⁻¹)(w)` for every tangent vector `w`. -/
noncomputable def tangentialGradient (f : M → ℝ) (x : M) : EuclideanSpace ℝ (Fin (n + 2)) :=
  (ambientTangentSpace ι x).starProjection
    ((InnerProductSpace.toDual ℝ _).symm
      (fderivWithin ℝ (Function.extend ι f 0) (Set.range ι) (ι x)))

/-- The divergence at `ι x` of a tangent vector field `X : M → ℝ^{n+2}` along `Set.range ι`,
with respect to the metric induced by `ι`: the trace over the tangent space at `ι x` of the map
`v ↦ P (D_v X)`, where `D_v X` is the derivative of `X ∘ ι⁻¹` along `Set.range ι` in the
tangent direction `v` and `P` is the orthogonal projection onto the tangent space. By the Gauss
formula, `v ↦ P (D_v X)` is the Levi-Civita covariant derivative of `X`, so this is the
Riemannian divergence. -/
noncomputable def tangentialDivergence (X : M → EuclideanSpace ℝ (Fin (n + 2))) (x : M) : ℝ :=
  LinearMap.trace ℝ (ambientTangentSpace ι x)
    ((ambientTangentSpace ι x).orthogonalProjection ∘L
      fderivWithin ℝ (Function.extend ι X 0) (Set.range ι) (ι x) ∘L
        (ambientTangentSpace ι x).subtypeL)

/-- The Laplace–Beltrami operator `Δ f = div (∇ f)` of the metric induced by `ι` on `M`,
evaluated at `x`. With this sign convention `-Δ` is a nonnegative operator. -/
noncomputable def laplaceBeltrami (f : M → ℝ) (x : M) : ℝ :=
  tangentialDivergence ι (tangentialGradient ι f) x

/-- The mean curvature vector of `Set.range ι` in `ℝ^{n+2}` at `ι x`, namely the
Laplace–Beltrami operator applied to the position vector `ι` (componentwise). This equals the
trace of the second fundamental form of `Set.range ι ⊆ ℝ^{n+2}`. -/
noncomputable def meanCurvatureVector (x : M) : EuclideanSpace ℝ (Fin (n + 2)) :=
  ∑ k, laplaceBeltrami ι (fun y ↦ ι y k) x • EuclideanSpace.single k 1

/-- `Set.range ι ⊆ S^{n+1}` is a minimal submanifold of the unit sphere `S^{n+1}`: its mean
curvature vector in `S^{n+1}`, which is the component of the mean curvature vector in `ℝ^{n+2}`
tangent to the sphere, vanishes. Equivalently, at every point `p = ι x` the mean curvature
vector in `ℝ^{n+2}` is normal to the sphere, i.e. a multiple of `p` (by Takahashi's theorem it
is then equal to `-n • p`). -/
def IsMinimalInSphere : Prop :=
  ∀ x, meanCurvatureVector ι x ∈ ℝ ∙ ι x

/-- `μ` is an eigenvalue of `-Δ`, where `Δ` is the Laplace–Beltrami operator of the metric
induced by `ι` on `M`: there is a smooth function `f ≠ 0` on `M` with `-Δ f = μ f`. -/
def IsEigenvalue (μ : ℝ) : Prop :=
  ∃ f : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ) ∞ f ∧ f ≠ 0 ∧ ∀ x, -laplaceBeltrami ι f x = μ * f x

/-- **Yau's conjecture on the first eigenvalue** (Yau, 1982).
Let $n \geq 2$ and let $M^n$ be a closed (compact, without boundary) embedded minimal hypersurface
of the unit sphere $S^{n+1} \subseteq \mathbb{R}^{n+2}$. Then the first (nonzero) eigenvalue
$\lambda_1(M)$ of the Laplace–Beltrami operator $-\Delta$ of $M$ is equal to $n$, i.e. $n$ is the
least positive eigenvalue of $-\Delta$.

The hypersurface is given as a smooth embedding `ι` of a compact, nonempty, boundaryless smooth
`n`-manifold `M` into `ℝ^{n+2}` with image in the unit sphere. The restriction $n \geq 2$ excludes
the degenerate case $n = 0$ (a finite set of points has no positive eigenvalue) and the trivial
case $n = 1$ (closed embedded geodesics of $S^2$ are great circles, with $\lambda_1 = 1$).
The inequality $\lambda_1(M) \le n$ is known (Takahashi), so the open content is
$\lambda_1(M) \geq n$. -/
theorem yaus_conjecture_on_the_first_eigenvalue {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [CompactSpace M] [Nonempty M]
    (ι : M → EuclideanSpace ℝ (Fin (n + 2)))
    (hι : IsSmoothEmbedding (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 2))) ∞ ι)
    (hsphere : Set.range ι ⊆ Metric.sphere 0 1)
    (hmin : IsMinimalInSphere ι) :
    IsLeast {μ : ℝ | 0 < μ ∧ IsEigenvalue ι μ} n := by
  sorry

end YausConjectureOnTheFirstEigenvalue

theorem YausConjectureOnTheFirstEigenvalue.yaus_conjecture_on_the_first_eigenvalue.disproof : ¬ (type_of% @YausConjectureOnTheFirstEigenvalue.yaus_conjecture_on_the_first_eigenvalue) := sorry
