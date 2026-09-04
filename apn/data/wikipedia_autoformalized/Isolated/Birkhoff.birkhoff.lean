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
# Birkhoff conjecture

Let $\Omega \subset \mathbb{R}^2$ be a strictly convex billiard table, i.e. a bounded domain whose
boundary $\partial\Omega$ is a $C^2$ closed curve with strictly positive curvature. A billiard ball
moves in straight lines inside $\Omega$ and reflects elastically at $\partial\Omega$ (angle of
incidence equals angle of reflection). The *billiard map* $T$ acts on the phase space
$\partial\Omega \times (0, \pi)$, whose points are pairs (position on the boundary, angle between
the outgoing direction and the positively oriented tangent). The billiard is *integrable* if a
neighbourhood of the boundary $\partial\Omega \times \{0, \pi\}$ of the phase space is foliated by
homotopically non-trivial invariant curves of $T$. (Equivalently, a neighbourhood of
$\partial\Omega$ inside $\Omega$ is foliated by convex caustics.)

**Birkhoff conjecture.** If a billiard table is strictly convex and integrable, is its boundary
necessarily an ellipse? The conjectured answer is yes; ellipses (including circles) are integrable.

Note that the whole phase space is foliated by invariant curves only for disks: this is a
theorem of Bialy (1993), so the conjecture concerns integrability near the boundary.

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, George David Birkhoff](https://en.wikipedia.org/wiki/George_David_Birkhoff)
- [Wikipedia, Dynamical billiards](https://en.wikipedia.org/wiki/Dynamical_billiards)
- V. Kaloshin, A. Sorrentino, *On the local Birkhoff conjecture for convex billiards*,
  Ann. of Math. 188 (2018), [arXiv:1612.09194](https://arxiv.org/abs/1612.09194)
- M. Bialy, *Convex billiards and a theorem by E. Hopf*, Math. Z. 214 (1993), 147–154
-/

open Real
open scoped EuclideanGeometry

namespace Birkhoff

/--
A *strictly convex billiard table* is described by its boundary curve `γ`: a $C^2$ simple closed
curve in the plane, parametrised with period `1` and traversed counterclockwise, whose curvature
is everywhere strictly positive. The last condition is expressed as the positivity of the area
form $\gamma' \wedge \gamma''$; in particular it forces `γ` to be regular ($\gamma' \neq 0$).
-/
structure IsStrictlyConvexCurve (γ : ℝ → ℝ²) : Prop where
  contDiff : ContDiff ℝ 2 γ
  periodic : Function.Periodic γ 1
  injOn : Set.InjOn γ (Set.Ico 0 1)
  curvature_pos : ∀ s, 0 < positiveOrientation.areaForm (deriv γ s) (iteratedDeriv 2 γ s)

/-- The unit tangent vector of the curve `γ` at the parameter `s`. -/
noncomputable def unitTangent (γ : ℝ → ℝ²) (s : ℝ) : ℝ² :=
  ‖deriv γ s‖⁻¹ • deriv γ s

/--
The direction of the billiard ball leaving the boundary point `γ s` at angle `θ` with the
positively oriented tangent: the unit tangent rotated counterclockwise by `θ`. For a
counterclockwise curve and `θ ∈ (0, π)` this direction points into the table.
-/
noncomputable def direction (γ : ℝ → ℝ²) (s θ : ℝ) : ℝ² :=
  positiveOrientation.rotation (θ : Real.Angle) (unitTangent γ s)

/--
The billiard map of the table bounded by `γ`, as a relation on the phase space
$\mathbb{R} \times (0, \pi)$ (position parameter, angle with the tangent; the position is only
relevant modulo the period `1`). `BilliardRel γ (s, θ) (s', θ')` holds when the ball leaving
`γ s` in the direction `direction γ s θ` next hits the boundary at `γ s'`, and the direction
`direction γ s' θ'` in which it leaves `γ s'` is the mirror image of its incoming direction in
the tangent line at `γ s'` (law of reflection). For a strictly convex curve this relation is the
graph of the billiard map.
-/
def BilliardRel (γ : ℝ → ℝ²) (p q : ℝ × ℝ) : Prop :=
  p.2 ∈ Set.Ioo 0 π ∧ q.2 ∈ Set.Ioo 0 π ∧
    (∃ r > 0, γ q.1 = γ p.1 + r • direction γ p.1 p.2) ∧
    direction γ q.1 q.2 = (ℝ ∙ unitTangent γ q.1).reflection (direction γ p.1 p.2)

/--
A (homotopically non-trivial) *invariant curve* of the billiard map of the table bounded by `γ`,
written as the graph of a continuous function `f` from the boundary (parametrised with period `1`)
to the angles `(0, π)`. Invariance means that the billiard map sends the graph of `f` onto itself.
By Birkhoff's theorem on twist maps, every homotopically non-trivial closed invariant curve of the
billiard map is such a graph.
-/
structure IsInvariantCurve (γ : ℝ → ℝ²) (f : ℝ → ℝ) : Prop where
  continuous : Continuous f
  periodic : Function.Periodic f 1
  mem_Ioo : ∀ s, f s ∈ Set.Ioo 0 π
  forward_invariant : ∀ s q, BilliardRel γ (s, f s) q → q.2 = f q.1
  backward_invariant : ∀ p s, BilliardRel γ p (s, f s) → p.2 = f p.1

/--
The billiard in the table bounded by `γ` is *integrable* if a neighbourhood of the boundary
`{θ = 0} ∪ {θ = π}` of the phase space is foliated by invariant curves: there is a family `F`
of invariant curves with pairwise disjoint graphs whose union contains
$\mathbb{R} \times ((0, \varepsilon) \cup (\pi - \varepsilon, \pi))$ for some
$\varepsilon > 0$.
-/
def IsIntegrable (γ : ℝ → ℝ²) : Prop :=
  ∃ F : Set (ℝ → ℝ), (∀ f ∈ F, IsInvariantCurve γ f) ∧
    F.Pairwise (fun f g => ∀ s, f s ≠ g s) ∧
    ∃ ε > 0, ∀ s, ∀ θ ∈ Set.Ioo 0 ε ∪ Set.Ioo (π - ε) π, ∃ f ∈ F, f s = θ

/-- A subset of the plane is an *ellipse* if it is the image of the unit circle under an affine
automorphism of the plane. Circles are ellipses. -/
def IsEllipse (S : Set ℝ²) : Prop :=
  ∃ e : ℝ² ≃ᵃ[ℝ] ℝ², S = e '' Metric.sphere 0 1

/--
**Birkhoff conjecture.**
If a billiard table is strictly convex and integrable, is its boundary necessarily an ellipse?

Here a strictly convex table has a $C^2$ boundary with strictly positive curvature, and
integrability means that a neighbourhood of the boundary of the phase space is foliated by
invariant curves of the billiard map. The conjectured answer is yes.
-/
theorem birkhoff :
    ∀ γ : ℝ → ℝ², IsStrictlyConvexCurve γ → IsIntegrable γ →
      IsEllipse (Set.range γ) := by
  sorry

end Birkhoff

theorem Birkhoff.birkhoff.disproof : ¬ (type_of% @Birkhoff.birkhoff) := sorry
