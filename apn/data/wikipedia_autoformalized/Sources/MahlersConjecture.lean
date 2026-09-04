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
# Mahler's conjecture

Mahler's conjecture on the product of the volumes of a centrally symmetric convex body and
its polar.

A *convex body* in $\mathbb{R}^n$ is a compact convex set with nonempty interior. It is
*centrally symmetric* if $K = -K$. Its *polar body* is
$K^\circ = \{x \in \mathbb{R}^n \mid \langle x, y \rangle \le 1 \text{ for all } y \in K\}$,
and the *Mahler volume* of $K$ is $\operatorname{vol}(K) \cdot \operatorname{vol}(K^\circ)$.
Mahler's conjecture states that the Mahler volume of every centrally symmetric convex body in
$\mathbb{R}^n$ is at least $4^n / n!$, the Mahler volume of the cube $[-1, 1]^n$ (whose polar
body is the cross-polytope). The conjecture is known for $n \le 3$ and open for $n \ge 4$.

*References:*
- [Wikipedia, Mahler volume](https://en.wikipedia.org/wiki/Mahler_volume)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [IS20] H. Iriyeh, M. Shibata, *Symmetric Mahler's conjecture for the volume product in the
  3-dimensional case*, Duke Math. J. 169 (2020), 1077–1134.
  [arXiv:1706.01749](https://arxiv.org/abs/1706.01749)
- [Ma39] K. Mahler, *Ein Minimalproblem für konvexe Polygone*, Mathematica (Zutphen) B 7
  (1939), 118–127.
-/

open MeasureTheory

open scoped ENNReal EuclideanGeometry InnerProductSpace Pointwise

namespace MahlersConjecture

/--
The polar body of a set `K ⊆ ℝⁿ` (with respect to the origin):
$K^\circ = \{x \in \mathbb{R}^n \mid \langle x, y \rangle \le 1 \text{ for all } y \in K\}$.

Mathlib's `LinearMap.polar` is the *absolute* polar (defined by `|⟪x, y⟫| ≤ 1`); for centrally
symmetric `K` the two coincide, see `MahlersConjecture.polarBody_eq_polar`.
-/
def polarBody {n : ℕ} (K : Set (ℝ^n)) : Set (ℝ^n) :=
  {x | ∀ y ∈ K, ⟪x, y⟫_ℝ ≤ 1}

@[category API, AMS 52]
theorem mem_polarBody {n : ℕ} {K : Set (ℝ^n)} {x : ℝ^n} :
    x ∈ polarBody K ↔ ∀ y ∈ K, ⟪x, y⟫_ℝ ≤ 1 :=
  Iff.rfl

/-- The origin belongs to every polar body. -/
@[category test, AMS 52]
theorem zero_mem_polarBody {n : ℕ} (K : Set (ℝ^n)) : 0 ∈ polarBody K := by
  simp [polarBody]

/-- Taking polar bodies reverses inclusions. -/
@[category API, AMS 52]
theorem polarBody_subset_polarBody {n : ℕ} {K L : Set (ℝ^n)} (h : K ⊆ L) :
    polarBody L ⊆ polarBody K :=
  fun _ hx y hy => hx y (h hy)

/--
For a centrally symmetric set `K`, the polar body coincides with the absolute polar
`LinearMap.polar` of Mathlib (with respect to the standard inner product), which is
defined by the condition `|⟪x, y⟫| ≤ 1` for all `y ∈ K`.
-/
@[category API, AMS 52]
theorem polarBody_eq_polar {n : ℕ} {K : Set (ℝ^n)} (hK : -K = K) :
    polarBody K = (innerₗ (ℝ^n)).polar K := by
  ext x
  simp only [polarBody, Set.mem_setOf_eq, LinearMap.polar_mem_iff, innerₗ_apply_apply,
    Real.norm_eq_abs, abs_le, real_inner_comm]
  refine ⟨fun h y hy => ⟨?_, h y hy⟩, fun h y hy => (h y hy).2⟩
  have := h (-y) (by rw [← hK]; simpa using hy)
  rw [inner_neg_right] at this
  linarith

/-- The polar body of the closed unit ball is the closed unit ball. -/
@[category test, AMS 52]
theorem polarBody_closedBall {n : ℕ} :
    polarBody (Metric.closedBall (0 : ℝ^n) 1) = Metric.closedBall 0 1 := by
  ext x
  simp only [polarBody, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro h
    by_cases hx : x = 0
    · simp [hx]
    · have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have := h (‖x‖⁻¹ • x)
        (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx'.ne'])
      rwa [inner_smul_right, real_inner_self_eq_norm_sq, pow_two, inv_mul_cancel_left₀ hx'.ne']
        at this
  · intro h y hy
    exact (real_inner_le_norm x y).trans (by nlinarith [norm_nonneg x, norm_nonneg y])

/--
**Mahler's conjecture** (symmetric case). Let $n \ge 1$ and let $K \subseteq \mathbb{R}^n$ be a
centrally symmetric convex body, i.e. a compact convex set with nonempty interior such that
$K = -K$. Let $K^\circ = \{x \mid \langle x, y \rangle \le 1 \text{ for all } y \in K\}$ be its
polar body. Then the product of the volumes of $K$ and $K^\circ$ satisfies
$$\operatorname{vol}(K) \cdot \operatorname{vol}(K^\circ) \ge \frac{4^n}{n!},$$
the value attained by the cube $[-1, 1]^n$ (whose polar body is the cross-polytope).

The conjecture is known for $n \le 3$ (Mahler for $n = 2$ [Ma39], Iriyeh and Shibata for
$n = 3$ [IS20]) and open for $n \ge 4$.
-/
@[category research open, AMS 52]
theorem mahlers_conjecture (n : ℕ) (hn : 1 ≤ n) (K : Set (ℝ^n)) (hK_compact : IsCompact K)
    (hK_convex : Convex ℝ K) (hK_int : (interior K).Nonempty) (hK_symm : -K = K) :
    (4 : ℝ≥0∞) ^ n / n.factorial ≤ volume K * volume (polarBody K) := by
  sorry

/--
**Mahler's conjecture** in dimension $2$, proved by Mahler [Ma39]: every centrally symmetric
convex body $K \subseteq \mathbb{R}^2$ satisfies
$\operatorname{vol}(K) \cdot \operatorname{vol}(K^\circ) \ge 4^2 / 2! = 8$.
-/
@[category research solved, AMS 52]
theorem mahlers_conjecture.variants.dim_two (K : Set (ℝ^2)) (hK_compact : IsCompact K)
    (hK_convex : Convex ℝ K) (hK_int : (interior K).Nonempty) (hK_symm : -K = K) :
    8 ≤ volume K * volume (polarBody K) := by
  sorry

/--
**Mahler's conjecture** in dimension $3$, proved by Iriyeh and Shibata [IS20]: every centrally
symmetric convex body $K \subseteq \mathbb{R}^3$ satisfies
$\operatorname{vol}(K) \cdot \operatorname{vol}(K^\circ) \ge 4^3 / 3! = 32/3$.
-/
@[category research solved, AMS 52]
theorem mahlers_conjecture.variants.dim_three (K : Set (ℝ^3)) (hK_compact : IsCompact K)
    (hK_convex : Convex ℝ K) (hK_int : (interior K).Nonempty) (hK_symm : -K = K) :
    32 / 3 ≤ volume K * volume (polarBody K) := by
  sorry

end MahlersConjecture
