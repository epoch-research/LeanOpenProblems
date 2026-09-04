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
# Ulam's packing conjecture

Ulam's packing conjecture concerns the identity of the worst-packing convex solid in
three-dimensional Euclidean space. It says that the optimal density for packing congruent copies
of a ball is smaller than that for any other convex body: the ball is the convex solid which
forces the largest fraction of space to remain empty in its optimal packing. By Hales's proof of
the Kepler conjecture, $\delta(B^3) = \pi / \sqrt{18} \approx 0.7405$, so the conjecture says that
no convex solid forces more than $\approx 25.95\%$ of space to remain empty.

We follow the definitions of [Ka15, §1]. A *convex body* is a compact convex subset of
$\mathbb{R}^3$ with nonempty interior. A set $\Xi$ of isometries of $\mathbb{R}^3$ is *admissible*
for $K$ (produces a *packing* of $K$) if the interiors of $\xi(K)$ and $\xi'(K)$ are disjoint for
all distinct $\xi, \xi' \in \Xi$. The *(upper) density* of the packing $\{\xi(K) : \xi \in \Xi\}$
is the fraction of space it fills,
$$\limsup_{r \to \infty} \frac{\operatorname{vol}\big(\bigcup_{\xi \in \Xi} \xi(K) \cap
  B(0, r)\big)}{\operatorname{vol}(B(0, r))},$$
and the *packing density* $\delta(K)$ is the supremum of the densities of all packings of $K$.

The main statement `ulams_packing_conjecture` is the non-strict form "the ball is a global minimum
of $\delta$" used in [Ka14] and [Ka15]. The strict form "the ball packs strictly worse than every
other convex body", which is how the Wikipedia article phrases the conjecture, is
`ulams_packing_conjecture.variants.strict`. Isometries include reflections; the variant
`ulams_packing_conjecture.variants.rigid_motions` only allows orientation-preserving isometries
(rotations and translations), as for physically identical solids.

*References:*
- [Wikipedia, Ulam's packing conjecture](https://en.wikipedia.org/wiki/Ulam%27s_packing_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Ga95] Gardner, M., *New Mathematical Diversions* (revised edition), MAA, 1995, postscript to
  the chapter "Packing Spheres".
- [Ka14] Kallus, Y., *The 3-ball is a local pessimum for packing*, Adv. Math. 264 (2014),
  355–370. [arXiv:1212.2551](https://arxiv.org/abs/1212.2551)
- [Ka15] Kallus, Y., *Pessimal packing shapes*, Geom. Topol. 19 (2015), 343–363.
  [arXiv:1305.0289](https://arxiv.org/abs/1305.0289)
- [Ha05] Hales, T. C., *A proof of the Kepler conjecture*, Ann. of Math. 162 (2005), 1065–1185.
-/

open MeasureTheory Filter
open scoped EuclideanGeometry ENNReal Real

namespace UlamsPackingConjecture

/-- A set `Ξ` of isometries of $\mathbb{R}^3$ is *admissible* for a set `K`, i.e. produces a
**packing** of `K`, if the congruent copies $\xi(K)$, $\xi \in \Xi$, have pairwise disjoint
interiors. Touching copies are allowed, as is standard for packings (see [Ka15, §1]). -/
def IsPacking (K : Set ℝ³) (Ξ : Set (ℝ³ ≃ᵢ ℝ³)) : Prop :=
  Ξ.PairwiseDisjoint fun ξ => interior (ξ '' K)

/-- The **(upper) density** of the family of congruent copies $\{\xi(K) : \xi \in \Xi\}$ of `K`:
the `limsup`, as $r \to \infty$, of the fraction of the ball of radius $r$ about the origin that
is covered by the union $\bigcup_{\xi \in \Xi} \xi(K)$. -/
noncomputable def upperDensity (K : Set ℝ³) (Ξ : Set (ℝ³ ≃ᵢ ℝ³)) : ℝ≥0∞ :=
  limsup (fun r : ℝ =>
    volume ((⋃ ξ ∈ Ξ, ξ '' K) ∩ Metric.ball 0 r) / volume (Metric.ball (0 : ℝ³) r)) atTop

/-- The **packing density** $\delta(K)$ of a set `K` in $\mathbb{R}^3$: the supremum of the upper
densities of all packings of $\mathbb{R}^3$ by congruent copies of `K`, where the copies may be
moved by arbitrary isometries (see [Ka15, §1]). -/
noncomputable def packingDensity (K : Set ℝ³) : ℝ≥0∞ :=
  ⨆ (Ξ : Set (ℝ³ ≃ᵢ ℝ³)) (_ : IsPacking K Ξ), upperDensity K Ξ

/-- An isometry of $\mathbb{R}^3$ is a *rigid motion* (an orientation-preserving isometry, i.e. a
rotation followed by a translation) if the determinant of its linear part is positive. -/
def IsRigidMotion (ξ : ℝ³ ≃ᵢ ℝ³) : Prop :=
  0 < LinearMap.det (ξ.toRealAffineIsometryEquiv.linear : ℝ³ →ₗ[ℝ] ℝ³)

/-- The packing density of a set `K` in $\mathbb{R}^3$ when only packings by rigid motions
(rotations and translations, but no reflections) of `K` are allowed. -/
noncomputable def rigidPackingDensity (K : Set ℝ³) : ℝ≥0∞ :=
  ⨆ (Ξ : Set (ℝ³ ≃ᵢ ℝ³)) (_ : IsPacking K Ξ ∧ ∀ ξ ∈ Ξ, IsRigidMotion ξ), upperDensity K Ξ

/-- **Ulam's packing conjecture** for packings by rigid motions, i.e. for "identical convex
solids" [Ga95] that may be rotated and translated but not reflected: for every convex body
$K \subset \mathbb{R}^3$, the optimal density of packings of $\mathbb{R}^3$ by rigid-motion copies
of $K$ is at least the optimal density of packings by congruent balls. Since rigid-motion packings
are packings, this implies `ulams_packing_conjecture`. -/
theorem ulams_packing_conjecture.variants.rigid_motions (K : ConvexBody ℝ³)
    (hK : (interior (K : Set ℝ³)).Nonempty) :
    rigidPackingDensity (Metric.closedBall 0 1) ≤ rigidPackingDensity K := by
  sorry

end UlamsPackingConjecture

theorem UlamsPackingConjecture.ulams_packing_conjecture.variants.rigid_motions.disproof : ¬ (type_of% @UlamsPackingConjecture.ulams_packing_conjecture.variants.rigid_motions) := sorry
