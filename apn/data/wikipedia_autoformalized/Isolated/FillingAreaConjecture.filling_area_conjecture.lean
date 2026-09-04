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
# Filling area conjecture

Gromov's filling area conjecture (1983) asserts that the hemisphere has the minimum area among
the shortcut-free surfaces in Euclidean space whose boundary is a closed curve of given length.

More precisely, a compact surface $M$ *fills* a closed curve $C$ if its boundary $\partial M$ is
the curve $C$. The filling is *isometric* (or *shortcut-free*) if for any two points $x, y$ of
$C$ the intrinsic distance $d_M(x, y)$, the infimum of the lengths of the curves from $x$ to $y$
along $M$, is not less than the intrinsic distance $d_C(x, y)$ along the boundary curve. The
conjecture states that an orientable compact surface that isometrically fills a closed curve of
length $\ell$ has area at least $\ell^2 / (2\pi)$, the area of the hemisphere that fills a circle
of length $\ell$.

Gromov stated the conjecture for orientable compact Riemannian surfaces with boundary. By the Nash
embedding theorem, every such surface embeds isometrically and smoothly in some Euclidean space
$\mathbb{R}^n$, so the conjecture is equivalently a statement about compact orientable smooth
surfaces with boundary embedded in Euclidean space, with the length of curves and the area measured
in the ambient Euclidean space. This is the formulation used here.

*References:*
- [Wikipedia, Filling area conjecture](https://en.wikipedia.org/wiki/filling_area_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Gro83] Gromov, M., _Filling Riemannian manifolds_, J. Differential Geom. 18 (1983), 1–147.
-/

namespace FillingAreaConjecture

open Manifold MeasureTheory Set
open scoped ContDiff ENNReal EuclideanGeometry Real

section IntrinsicEDist

variable {X : Type*} [PseudoEMetricSpace X]

/-- The *intrinsic* extended distance between `x` and `y` inside a subset `s` of a metric space:
the infimum of the lengths (total variations) of the continuous paths from `x` to `y` that stay
inside `s`. It is `∞` when there is no such path. -/
noncomputable def intrinsicEDist (s : Set X) (x y : X) : ℝ≥0∞ :=
  ⨅ (γ : Path x y) (_ : range γ ⊆ s), eVariationOn γ univ

variable {s t : Set X} {x y : X}

end IntrinsicEDist

section IsOrientable

variable {k : ℕ} {H : Type*} [TopologicalSpace H]

/-- A `C^∞` manifold `M` (possibly with boundary or corners) modelled on `I` is *orientable* if it
admits an atlas of `C^∞` charts covering `M` all of whose transition maps have positive Jacobian
determinant. -/
def IsOrientable (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin k)) H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] : Prop :=
  ∃ 𝒜 : Set (OpenPartialHomeomorph M H), 𝒜 ⊆ IsManifold.maximalAtlas I ∞ M ∧
    (⋃ e ∈ 𝒜, e.source) = univ ∧
    ∀ e ∈ 𝒜, ∀ e' ∈ 𝒜,
      ∀ x ∈ (e.extend I).target ∩ (e.extend I).symm ⁻¹' e'.source,
        0 < (fderivWithin ℝ (e'.extend I ∘ (e.extend I).symm) (range I) x).det

end IsOrientable

/-- The closed upper hemisphere of radius `r` in `ℝ^3`: the points of the sphere of radius `r`
centred at the origin with nonnegative last coordinate. Its boundary is a circle of length
$2\pi r$ and its area is $2\pi r^2$. -/
def hemisphere (r : ℝ) : Set (ℝ^3) := Metric.sphere 0 r ∩ {p | 0 ≤ p 2}

/-- **Filling area conjecture** (Gromov, 1983): a hemisphere has the minimum area among the
shortcut-free (orientable) surfaces in Euclidean space whose boundary forms a closed curve of
given length.

Precisely, let `M` be a compact orientable `C^∞` surface with boundary, smoothly embedded in a
Euclidean space `ℝ^n` by `f`, whose boundary `∂M` is a single closed curve, of length `ℓ`.
Assume that $f(M)$ is a *shortcut-free* (isometric) filling of its boundary curve: for any two
points of the boundary curve, the intrinsic distance inside $f(M)$ is at least the intrinsic
distance along the boundary curve. Then the area of $f(M)$ is at least the area of the hemisphere
whose boundary circle has length `ℓ`, that is $\ell^2 / (2 \pi)$.

Lengths and areas are the one- and two-dimensional Hausdorff measures in the ambient Euclidean
space. Since Mathlib's Hausdorff measure `μH[d]` is not normalised to agree with Lebesgue measure
on Euclidean space, we compare the area of $f(M)$ with the (identically normalised) area of the
hemisphere of radius `ℓ / (2π)`, rather than with the numerical value $\ell^2 / (2 \pi)$. -/
theorem filling_area_conjecture (n : ℕ) (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] [IsManifold (𝓡∂ 2) ∞ M]
    (hM : IsOrientable (𝓡∂ 2) M)
    (f : M → ℝ^n) (hf : IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, ℝ^n) ∞ f)
    (hbd : Nonempty ((𝓡∂ 2).boundary M ≃ₜ Circle))
    (ℓ : ℝ) (hℓ : μH[1] (f '' (𝓡∂ 2).boundary M) = ENNReal.ofReal ℓ)
    (hfill : ∀ x ∈ f '' (𝓡∂ 2).boundary M, ∀ y ∈ f '' (𝓡∂ 2).boundary M,
      intrinsicEDist (f '' (𝓡∂ 2).boundary M) x y ≤ intrinsicEDist (range f) x y) :
    μH[2] (hemisphere (ℓ / (2 * π))) ≤ μH[2] (range f) := by
  sorry

end FillingAreaConjecture

theorem FillingAreaConjecture.filling_area_conjecture.disproof : ¬ (type_of% @FillingAreaConjecture.filling_area_conjecture) := sorry
