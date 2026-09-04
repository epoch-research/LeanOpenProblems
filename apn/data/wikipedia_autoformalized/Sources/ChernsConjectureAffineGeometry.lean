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
# Chern's conjecture (affine geometry)

Chern's conjecture for affinely flat manifolds (1955) states that the Euler characteristic of a
compact affine manifold vanishes.

An *affine manifold* is a manifold with an atlas modelled on $\mathbb{R}^n$ whose transition maps
are locally affine. Equivalently, it is a smooth manifold whose tangent bundle carries a flat
*torsion-free* connection: the affine charts are exactly the coordinate systems in which such a
connection is the standard flat one. Torsion-freeness is essential: Smillie constructed closed
manifolds with non-zero Euler characteristic whose tangent bundles admit flat connections with
torsion.

The conjecture is trivial in odd dimensions (by Poincaré duality) and is known when the manifold
is $2$-dimensional (Benzécri, Milnor), complete (Kostant–Sullivan), or carries a parallel volume
form (Klingler). It is open in general.

This file defines the Euler characteristic of a topological space through its rational singular
homology, and affine manifolds through the groupoid of locally affine maps.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Chern%27s_conjecture_%28affine_geometry%29)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Kl17] B. Klingler, *Chern's conjecture for special affine manifolds*, Ann. of Math. 186 (2017),
  69–95.
- [FZ17] H. Feng, W. Zhang, *Flat vector bundles and open coverings*,
  [arXiv:1603.07248](https://arxiv.org/abs/1603.07248)
-/

namespace ChernsConjectureAffineGeometry

open CategoryTheory AlgebraicTopology Filter Topology
open scoped Manifold ContDiff

universe u

section EulerCharacteristic

/-- The `k`-th Betti number of a topological space `X`: the dimension over $\mathbb{Q}$ of the
`k`-th singular homology group $H_k(X; \mathbb{Q})$ (the coefficient module `ℚ` is lifted to the
universe of `X`). It is `0` when this homology group is infinite-dimensional. -/
noncomputable def bettiNumber (X : Type u) [TopologicalSpace X] (k : ℕ) : ℕ :=
  Module.finrank ℚ
    (((singularHomologyFunctor (ModuleCat.{u} ℚ) k).obj (ModuleCat.of ℚ (ULift.{u} ℚ))).obj
      (TopCat.of X))

/-- The Euler characteristic $\chi(X) = \sum_k (-1)^k \dim_{\mathbb{Q}} H_k(X; \mathbb{Q})$ of a
topological space `X`, as a finite sum over all `k`. For a compact manifold the Betti numbers are
finite and vanish above the dimension, so this is the usual Euler characteristic. (For a space
with infinitely many non-zero Betti numbers `finsum` returns `0`, but no such space occurs here.)
-/
noncomputable def eulerCharacteristic (X : Type u) [TopologicalSpace X] : ℤ :=
  ∑ᶠ k : ℕ, (-1 : ℤ) ^ k * bettiNumber X k

/-- The zeroth Betti number of a point is $1$. -/
@[category test, AMS 55]
theorem bettiNumber_punit_zero : bettiNumber PUnit.{u + 1} 0 = 1 := by
  have e := (singularHomologyFunctorZeroOfTotallyDisconnectedSpace (ModuleCat.{u} ℚ)
    (ModuleCat.of ℚ (ULift.{u} ℚ)) (TopCat.of PUnit.{u + 1}) ≪≫
      ModuleCat.coprodIsoDirectSum _).toLinearEquiv
  rw [bettiNumber, e.finrank_eq]
  simp [Module.finrank_directSum]

/-- A point has no homology in positive degrees. -/
@[category test, AMS 55]
theorem bettiNumber_punit_of_ne_zero {k : ℕ} (hk : k ≠ 0) :
    bettiNumber PUnit.{u + 1} k = 0 := by
  have := ModuleCat.subsingleton_of_isZero
    (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat.{u} ℚ) k
      (ModuleCat.of ℚ (ULift.{u} ℚ)) (TopCat.of PUnit.{u + 1}) hk)
  exact Module.finrank_zero_of_subsingleton

/-- The Euler characteristic of a point is $1$. -/
@[category test, AMS 55]
theorem eulerCharacteristic_punit : eulerCharacteristic PUnit.{u + 1} = 1 := by
  rw [eulerCharacteristic,
    finsum_eq_single _ 0 fun k hk ↦ by simp [bettiNumber_punit_of_ne_zero hk]]
  simp [bettiNumber_punit_zero]

end EulerCharacteristic

section AffineGroupoid

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The pregroupoid of locally affine maps of a real normed space `E`: a map `f : E → E` has the
property on a set `u` if, near every point of `u`, it coincides with a continuous affine map
`E →ᴬ[ℝ] E`. When `E` is finite-dimensional every affine map is continuous, so this is the
usual notion of a locally affine map. -/
def affinePregroupoid : Pregroupoid E where
  property f u := ∀ x ∈ u, ∃ g : E →ᴬ[ℝ] E, f =ᶠ[𝓝 x] g
  comp {f g _ _} hf hg _ _ _ x hx := by
    obtain ⟨a, ha⟩ := hf x hx.1
    obtain ⟨b, hb⟩ := hg (f x) hx.2
    refine ⟨b.comp a, ?_⟩
    have hfc : ContinuousAt f x := a.continuous.continuousAt.congr ha.symm
    filter_upwards [ha, hfc.eventually hb] with y hy₁ hy₂
    simp [← hy₁, hy₂]
  id_mem x _ := ⟨ContinuousAffineMap.id ℝ E, Eventually.of_forall fun _ ↦ rfl⟩
  locality _ h x hx :=
    let ⟨_, _, hxv, hv⟩ := h x hx
    hv x ⟨hx, hxv⟩
  congr hu hfg hf x hx :=
    let ⟨a, ha⟩ := hf x hx
    ⟨a, (eventuallyEq_of_mem (hu.mem_nhds hx) hfg).trans ha⟩

/-- The groupoid of locally affine open partial homeomorphisms of a real normed space `E`.

A charted space `M` modelled on `E` with `HasGroupoid M (affineGroupoid E)` is an *affine
manifold*: the transition maps between any two charts of its atlas are locally affine. -/
def affineGroupoid : StructureGroupoid E := (affinePregroupoid E).groupoid

/-- Locally affine maps are smooth, so the affine groupoid is contained in every `C^n` groupoid. -/
@[category API, AMS 53 57]
theorem affineGroupoid_le_contDiffGroupoid (n : WithTop ℕ∞) :
    affineGroupoid E ≤ contDiffGroupoid n 𝓘(ℝ, E) := by
  refine groupoid_of_pregroupoid_le _ _ fun f s hf ↦ ?_
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ]
  intro x hx
  obtain ⟨a, ha⟩ := hf x hx
  exact (a.contDiff.contDiffAt.congr_of_eventuallyEq ha).contDiffWithinAt

/-- An affine manifold is a smooth manifold. -/
@[category API, AMS 53 57]
instance IsManifold.of_hasGroupoid_affineGroupoid {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [HasGroupoid M (affineGroupoid E)] : IsManifold 𝓘(ℝ, E) ∞ M :=
  IsManifold.mk' _ _ _
    (gr := hasGroupoid_of_le inferInstance (affineGroupoid_le_contDiffGroupoid E ∞))

end AffineGroupoid

/-- **Chern's conjecture (affine geometry).** Let $M$ be a compact affine manifold of dimension
$n \geq 1$, that is, a compact Hausdorff manifold with an atlas modelled on $\mathbb{R}^n$ whose
transition maps are locally affine (equivalently, a closed smooth manifold whose tangent bundle
carries a flat torsion-free connection). Then the Euler characteristic of $M$ vanishes:
$\chi(M) = 0$.

Here `M` is a compact Hausdorff space charted on all of $\mathbb{R}^n$, hence a closed manifold
(second countability follows from compactness, and smoothness from the affine atlas, see
`IsManifold.of_hasGroupoid_affineGroupoid`). `M` is not assumed connected or orientable, and
`eulerCharacteristic M` is the alternating sum of the rational Betti numbers of `M`. The
zero-dimensional case is excluded because a single point is a compact affine manifold with
$\chi = 1$ (see `eulerCharacteristic_punit`); for odd $n$ the statement is a consequence of
Poincaré duality. -/
@[category research open, AMS 53 57]
theorem cherns_conjecture_affine_geometry (n : ℕ) (hn : 0 < n) (M : Type*) [TopologicalSpace M]
    [T2Space M] [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [HasGroupoid M (affineGroupoid (EuclideanSpace ℝ (Fin n)))] :
    eulerCharacteristic M = 0 := by
  sorry

end ChernsConjectureAffineGeometry
