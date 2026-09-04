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
# Carathéodory conjecture

The **Carathéodory conjecture** states that any convex, closed and twice-differentiable surface
in three-dimensional Euclidean space admits at least two umbilical points, i.e. points at which
the two principal curvatures coincide (equivalently, the second fundamental form is a scalar
multiple of the first fundamental form).

A closed convex surface is modelled as the boundary $\partial K$ of a compact convex body
$K \subseteq \mathbb{R}^3$ with nonempty interior. The surface is $C^2$ when it is locally a
regular level set of a $C^2$ function $F$; a point $p$ of such a surface is umbilical when the
Hessian of $F$ at $p$, restricted to the tangent plane $\ker dF_p$, is a scalar multiple of the
inner product. This is the classical notion: the second fundamental form at $p$ is
$-\mathrm{Hess}\,F_p / \|\nabla F(p)\|$ on the tangent plane, for any local defining function
$F$. Flat points (both principal curvatures zero) count as umbilical.

The conjecture is known for real-analytic surfaces (Hamburger). Guilfoyle and Klingenberg
have claimed a proof for $C^{3,\alpha}$ surfaces, and Alpöge has announced a $C^\infty$
counterexample; the conjecture is currently listed as open.

*References:*
- [Wikipedia: Carathéodory conjecture](https://en.wikipedia.org/wiki/Carath%C3%A9odory_conjecture)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- M. Ghomi, R. Howard, *Normal curvatures of asymptotically constant graphs and Carathéodory's
  conjecture*, Proc. Amer. Math. Soc. 140 (2012), [arXiv:1101.3031](https://arxiv.org/abs/1101.3031)
- B. Guilfoyle, W. Klingenberg, *Proof of the Carathéodory conjecture*,
  [arXiv:0808.0851](https://arxiv.org/abs/0808.0851)
-/

open Topology
open scoped EuclideanGeometry InnerProductSpace

namespace CaratheodoryConjecture

/-- `F` is a *local $C^2$ defining function* for the set `S ⊆ ℝ³` at the point `p`: `F` is twice
continuously differentiable near `p`, its derivative at `p` is nonzero (so its zero set is a
regular surface near `p`), and `S` coincides with the zero set of `F` in a neighbourhood of `p`. -/
structure IsLocalDefiningFunction (S : Set ℝ³) (p : ℝ³) (F : ℝ³ → ℝ) : Prop where
  contDiffAt : ContDiffAt ℝ 2 F p
  fderiv_ne_zero : fderiv ℝ F p ≠ 0
  eventually_mem_iff : ∀ᶠ x in 𝓝 p, x ∈ S ↔ F x = 0

/-- A set `S ⊆ ℝ³` is a *$C^2$ surface* (an embedded, twice continuously differentiable surface)
if near each of its points it is a regular level set of a $C^2$ function. -/
def IsC2Surface (S : Set ℝ³) : Prop :=
  ∀ p ∈ S, ∃ F : ℝ³ → ℝ, IsLocalDefiningFunction S p F

/-- A point `p` of a set `S ⊆ ℝ³` is an *umbilical point* of `S` if `S` has a local $C^2$ defining
function `F` at `p` whose Hessian at `p`, restricted to the tangent plane $\ker dF_p$, is a scalar
multiple `κ` of the inner product. Since the second fundamental form of a $C^2$ surface at `p` is
$-\mathrm{Hess}\,F_p / \|\nabla F(p)\|$ on the tangent plane, this says exactly that the two
principal curvatures of `S` at `p` coincide (including the case where both vanish). -/
def IsUmbilicalPoint (S : Set ℝ³) (p : ℝ³) : Prop :=
  p ∈ S ∧ ∃ F : ℝ³ → ℝ, IsLocalDefiningFunction S p F ∧ ∃ κ : ℝ,
    ∀ v w : ℝ³, fderiv ℝ F p v = 0 → fderiv ℝ F p w = 0 →
      fderiv ℝ (fderiv ℝ F) p v w = κ * ⟪v, w⟫_ℝ

/-- The function $x \mapsto \|x\|^2 - 1$ is a local defining function for the unit sphere at each
of its points. -/
@[category test, AMS 53]
theorem isLocalDefiningFunction_sphere (p : ℝ³) (hp : p ∈ Metric.sphere (0 : ℝ³) 1) :
    IsLocalDefiningFunction (Metric.sphere (0 : ℝ³) 1) p (fun x ↦ ‖x‖ ^ 2 - 1) where
  contDiffAt := ((contDiff_id.norm_sq ℝ).sub contDiff_const).contDiffAt
  fderiv_ne_zero := by
    have h : fderiv ℝ (fun x : ℝ³ ↦ ‖x‖ ^ 2 - 1) p = 2 • innerSL ℝ p :=
      ((hasStrictFDerivAt_norm_sq p).hasFDerivAt.sub_const 1).fderiv
    rw [h]
    intro h0
    have := congrArg (fun L : ℝ³ →L[ℝ] ℝ ↦ L p) h0
    simp [mem_sphere_zero_iff_norm.mp hp] at this
  eventually_mem_iff := Filter.Eventually.of_forall fun x ↦ by
    simp [sub_eq_zero, pow_eq_one_iff_of_nonneg (norm_nonneg x) two_ne_zero]

/-- The unit sphere is a $C^2$ surface. -/
@[category test, AMS 53]
theorem isC2Surface_sphere : IsC2Surface (Metric.sphere (0 : ℝ³) 1) :=
  fun p hp ↦ ⟨_, isLocalDefiningFunction_sphere p hp⟩

/-- Every point of the unit sphere is umbilical. -/
@[category test, AMS 53]
theorem isUmbilicalPoint_sphere (p : ℝ³) (hp : p ∈ Metric.sphere (0 : ℝ³) 1) :
    IsUmbilicalPoint (Metric.sphere (0 : ℝ³) 1) p := by
  refine ⟨hp, _, isLocalDefiningFunction_sphere p hp, 2, fun v w _ _ ↦ ?_⟩
  have h : fderiv ℝ (fun x : ℝ³ ↦ ‖x‖ ^ 2 - 1) = fun x ↦ (2 • innerSL ℝ) x := by
    ext x : 1
    exact ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const 1).fderiv
  rw [h, ContinuousLinearMap.fderiv]
  simp

/--
**Carathéodory conjecture.** Any convex, closed and twice-differentiable surface in
three-dimensional Euclidean space admits at least two umbilical points.

Precisely: let $K \subseteq \mathbb{R}^3$ be a compact convex set with nonempty interior whose
boundary $\partial K$ is a $C^2$ surface. Then $\partial K$ has at least two distinct umbilical
points, i.e. points at which the two principal curvatures coincide.
-/
@[category research open, AMS 52 53]
theorem caratheodory_conjecture (K : Set ℝ³) (hK : Convex ℝ K) (hKc : IsCompact K)
    (hKi : (interior K).Nonempty) (hS : IsC2Surface (frontier K)) :
    ∃ p q, p ≠ q ∧ IsUmbilicalPoint (frontier K) p ∧ IsUmbilicalPoint (frontier K) q := by
  sorry

end CaratheodoryConjecture
