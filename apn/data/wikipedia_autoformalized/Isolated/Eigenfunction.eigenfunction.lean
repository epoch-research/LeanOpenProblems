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
# Quantum unique ergodicity for eigenfunctions of the Laplacian

The quantum unique ergodicity (QUE) conjecture of Rudnick and Sarnak concerns the distribution of
large-frequency eigenfunctions of the Laplace–Beltrami operator on a compact Riemannian manifold
$M$ without boundary with strictly negative sectional curvature. It asserts that for *every*
sequence $(\varphi_k)$ of $L^2$-normalised eigenfunctions, $\Delta \varphi_k = \lambda_k \varphi_k$
with $\lambda_k \to \infty$, the probability measures $|\varphi_k|^2 \, d\mathrm{vol}$ converge
weakly to the normalised Riemannian volume $d\mathrm{vol} / \mathrm{vol}(M)$. This strengthens the
quantum ergodicity theorem of Shnirelman, Zelditch and Colin de Verdière, which gives this
conclusion only along a subsequence of density one.

This file states the conjecture on the manifold $M$ itself (convergence of the measures
$|\varphi_k|^2 \, d\mathrm{vol}$). The phase-space version, that Liouville measure is the only
quantum limit of the microlocal lifts on the unit cotangent bundle, is stronger and is not stated
here.

Mathlib has Riemannian manifolds (`IsRiemannianManifold`), but no Laplace–Beltrami operator,
Riemannian volume measure or curvature tensor. This file defines these notions from existing
primitives:

* the Riemannian volume is realised as the `n`-dimensional Hausdorff measure of the Riemannian
  distance (`n = dim M`), which is a positive constant multiple of the Riemannian volume; the
  constant disappears after normalisation;
* eigenfunctions of the Laplacian are defined through the weak form of the eigenvalue equation
  $\int_M \langle \nabla \varphi, \nabla \psi \rangle = \lambda \int_M \varphi \psi$ for all smooth
  $\psi$, which on a compact manifold without boundary is equivalent to
  $\Delta \varphi = \lambda \varphi$ for the non-negative Laplacian
  $\Delta = -\operatorname{div} \nabla$;
* the sectional curvature is computed from the Christoffel symbols of the metric coefficients in
  the preferred chart at each point.

*References:*
* [Wikipedia, Eigenfunction](https://en.wikipedia.org/wiki/eigenfunction)
* [Wikipedia, Quantum ergodicity](https://en.wikipedia.org/wiki/Quantum_ergodicity)
* [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [RS94] Z. Rudnick, P. Sarnak, *The behaviour of eigenstates of arithmetic hyperbolic
  manifolds*, Comm. Math. Phys. 161 (1994), 195–213.
* [Sa11] P. Sarnak, *Recent progress on the quantum unique ergodicity conjecture*,
  Bull. Amer. Math. Soc. 48 (2011), 211–228.
-/

open Bundle MeasureTheory Filter Topology
open scoped Manifold ContDiff

namespace Eigenfunction

/-
Throughout, `M` is a Riemannian manifold modelled on a finite-dimensional real vector space `E`:
its tangent spaces carry inner products (`RiemannianBundle`), and its extended distance is the
Riemannian distance (`IsRiemannianManifold I M`).
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The tangent spaces of a manifold modelled on a finite-dimensional space are
finite-dimensional. -/
local instance (x : M) : FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

/- ### Riemannian volume and the Laplace–Beltrami operator -/

/-- The normalised `n`-dimensional Hausdorff measure of an extended metric space `M`.

When `M` is a compact `n`-dimensional Riemannian manifold whose distance is the Riemannian
distance, the `n`-dimensional Hausdorff measure is a positive constant multiple of the
Riemannian volume, so `normalizedVolume M n` is the normalised Riemannian volume
$d\mathrm{vol} / \mathrm{vol}(M)$. -/
noncomputable def normalizedVolume (M : Type*) [EMetricSpace M] [MeasurableSpace M]
    [BorelSpace M] (n : ℕ) : Measure M :=
  (μH[n] (Set.univ : Set M))⁻¹ • μH[n]

/-- The Riemannian gradient of a function `φ : M → ℝ` at `x`: the tangent vector at `x`
representing the differential `dφ_x` through the Riemannian inner product on `TangentSpace I x`.
-/
noncomputable def gradient (φ : M → ℝ) (x : M) : TangentSpace I x :=
  (InnerProductSpace.toDual ℝ (TangentSpace I x)).symm (mfderiv I 𝓘(ℝ) φ x)

/-- `IsLaplaceEigenfunction I φ l` means that `φ : M → ℝ` is a smooth eigenfunction of the
Laplace–Beltrami operator with eigenvalue `l`, in weak form: for every smooth `ψ : M → ℝ`,
$$\int_M \langle \nabla \varphi, \nabla \psi \rangle \, d\mathrm{vol}
  = l \int_M \varphi \, \psi \, d\mathrm{vol}.$$
On a compact manifold without boundary, Green's formula shows that this is equivalent to
$\Delta \varphi = l \varphi$ for the non-negative Laplace–Beltrami operator
$\Delta = -\operatorname{div} \nabla$. Eigenfunctions of the Laplacian are smooth by elliptic
regularity, so requiring `φ` to be smooth loses no generality. -/
def IsLaplaceEigenfunction [MeasurableSpace M] [BorelSpace M] (φ : M → ℝ) (l : ℝ) : Prop :=
  ContMDiff I 𝓘(ℝ) ∞ φ ∧ ∀ ψ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ ψ →
    ∫ x, ⟪gradient I φ x, gradient I ψ x⟫ ∂(normalizedVolume M (Module.finrank ℝ E)) =
      l * ∫ x, φ x * ψ x ∂(normalizedVolume M (Module.finrank ℝ E))

/-
### Sectional curvature

The curvature at a point `x₀` is computed in the preferred chart `e = extChartAt I x₀`. A vector
`v : E` is identified with the coordinate vector field `y ↦ D(e⁻¹)_y v`. The metric coefficients,
the Christoffel symbols and the Riemann tensor are then given by the classical coordinate
formulas, using that coordinate vector fields commute.
-/

/-- The metric coefficients of the Riemannian metric in the chart `e = extChartAt I x₀`, at the
coordinate point `y : E`: the bilinear form `(v, w) ↦ ⟪D(e⁻¹)_y v, D(e⁻¹)_y w⟫` on `E`. -/
noncomputable def metricCoord (x₀ : M) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y)
    (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y)

/-- The Christoffel symbols of the first kind in the chart `extChartAt I x₀`:
`christoffelFirst I x₀ y u v w = ½ (∂ᵤ g(v, w) + ∂ᵥ g(u, w) - ∂_w g(u, v))`, that is,
`g(∇ᵤ v, w)` for the coordinate vector fields `u`, `v`, `w`. Here `D = fderiv ℝ g y`, so that
`D u v w = ∂ᵤ g(v, w)` and `(D.flip u).flip v w = D w u v = ∂_w g(u, v)`. -/
noncomputable def christoffelFirst (x₀ : M) (y : E) (u v : E) : E →L[ℝ] ℝ :=
  let D := fderiv ℝ (metricCoord I x₀) y
  (1 / 2 : ℝ) • (D u v + D v u - (D.flip u).flip v)

/-- The Christoffel symbols of the second kind in the chart `extChartAt I x₀`: the coordinate
vector `Γ(u, v) = ∇ᵤ v` characterised by `g(Γ(u, v), w) = christoffelFirst I x₀ y u v w` for all
`w`. It is obtained by inverting the metric coefficients; `ContinuousLinearMap.inverse` is the
genuine inverse because `metricCoord I x₀ y` is a linear isomorphism `E ≃ E*` for `y` in the
open target of the chart. -/
noncomputable def christoffel (x₀ : M) (y : E) (u v : E) : E :=
  (metricCoord I x₀ y).inverse (christoffelFirst I x₀ y u v)

/-- The Riemann curvature endomorphism `R(u, v) w = ∇ᵤ ∇ᵥ w - ∇ᵥ ∇ᵤ w` in the chart
`extChartAt I x₀`, for coordinate vector fields `u`, `v`, `w` (which commute):
`R(u, v) w = ∂ᵤ Γ(v, w) - ∂ᵥ Γ(u, w) + Γ(u, Γ(v, w)) - Γ(v, Γ(u, w))`. -/
noncomputable def riemann (x₀ : M) (y : E) (u v w : E) : E :=
  fderiv ℝ (fun z ↦ christoffel I x₀ z v w) y u - fderiv ℝ (fun z ↦ christoffel I x₀ z u w) y v
    + christoffel I x₀ y u (christoffel I x₀ y v w) - christoffel I x₀ y v (christoffel I x₀ y u w)

/-- The sectional curvature of `M` at `x₀` along the plane spanned by the tangent vectors with
coordinates `u` and `v` in the chart `extChartAt I x₀`:
$$K(u, v) = \frac{g(R(u, v) v, u)}{g(u, u) g(v, v) - g(u, v)^2}.$$
It is only meaningful when `u` and `v` are linearly independent. With these conventions the
round sphere has `K = 1` and hyperbolic space has `K = -1`. -/
noncomputable def sectionalCurvature (x₀ : M) (u v : E) : ℝ :=
  let y := extChartAt I x₀ x₀
  let g := metricCoord I x₀ y
  g (riemann I x₀ y u v v) u / (g u u * g v v - (g u v) ^ 2)

variable (M) in
/-- The Riemannian manifold `M` has strictly negative sectional curvature: at every point, the
sectional curvature of every tangent `2`-plane is negative. -/
def HasNegativeSectionalCurvature : Prop :=
  ∀ x₀ : M, ∀ u v : E, LinearIndependent ℝ ![u, v] → sectionalCurvature I x₀ u v < 0

/- ### The conjecture -/

/-- **Quantum unique ergodicity conjecture** (Rudnick–Sarnak). Let $M$ be a compact connected
smooth Riemannian manifold without boundary with strictly negative sectional curvature. Then for
every sequence $(\varphi_k)$ of $L^2$-normalised eigenfunctions of the Laplace–Beltrami operator,
$\Delta \varphi_k = \lambda_k \varphi_k$ with $\lambda_k \to \infty$, the measures
$|\varphi_k|^2 \, d\mathrm{vol}$ converge weakly to the normalised Riemannian volume:
$$\int_M f \, |\varphi_k|^2 \, d\mathrm{vol} \longrightarrow
  \frac{1}{\mathrm{vol}(M)} \int_M f \, d\mathrm{vol}$$
for every continuous $f : M \to \mathbb{R}$. Here $d\mathrm{vol}$ is normalised to a probability
measure. Eigenfunctions are taken real-valued; since the Laplacian is a real operator, this is
equivalent to the formulation with complex-valued eigenfunctions. Connectedness is part of the
usual meaning of "manifold" here; without it the statement fails for eigenfunctions supported on
a single component. -/
theorem eigenfunction [IsManifold I ∞ M]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompactSpace M] [ConnectedSpace M] [BoundarylessManifold I M]
    [MeasurableSpace M] [BorelSpace M]
    (hM : HasNegativeSectionalCurvature I M)
    (φ : ℕ → M → ℝ) (l : ℕ → ℝ) (hφ : ∀ k, IsLaplaceEigenfunction I (φ k) (l k))
    (hnorm : ∀ k, ∫ x, φ k x ^ 2 ∂(normalizedVolume M (Module.finrank ℝ E)) = 1)
    (hl : Tendsto l atTop atTop) (f : C(M, ℝ)) :
    Tendsto (fun k ↦ ∫ x, f x * φ k x ^ 2 ∂(normalizedVolume M (Module.finrank ℝ E))) atTop
      (𝓝 (∫ x, f x ∂(normalizedVolume M (Module.finrank ℝ E)))) := by
  sorry

/- ### Tests of the definitions -/

section VectorSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

end VectorSpace

end Eigenfunction

theorem Eigenfunction.eigenfunction.disproof : ¬ (type_of% @Eigenfunction.eigenfunction) := sorry
