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
# Danzer sets

A *Danzer set* in $\mathbb{R}^d$ is a set of points that meets every convex body of volume $1$.
Danzer asked whether such a set can have bounded density, i.e. growth rate $O(r^d)$.
Conway's *dead fly problem* (also due to Boshernitzan) asks whether such a set can be
uniformly discrete, i.e. whether distinct points of the set can be kept at least some fixed
positive distance apart. Both problems are open.

*References:*
- [Wikipedia, Danzer set](https://en.wikipedia.org/wiki/Danzer_set)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Ad22] Adiceam, F., _Around the Danzer problem and the construction of dense forests_.
  L'Enseignement Mathématique 68 (2022). [arXiv:2010.06756](https://arxiv.org/abs/2010.06756)
- [SoWe16] Solomon, Y. and Weiss, B., _Dense forests and Danzer sets_.
  Ann. Sci. Éc. Norm. Supér. 49 (2016). [arXiv:1406.3807](https://arxiv.org/abs/1406.3807)
- [SSW17] Solan, O., Solomon, Y. and Weiss, B., _On problems of Danzer and Gowers and dynamics
  on the space of closed subsets of $\mathbb{R}^d$_. IMRN (2017).
  [arXiv:1510.07179](https://arxiv.org/abs/1510.07179)
-/

open MeasureTheory Metric

open scoped EuclideanGeometry

namespace DanzerSet

/-- A set `S ⊆ ℝ^d` is a *Danzer set* if it intersects every convex body (compact convex
nonempty set) of volume `1`. -/
def IsDanzerSet {d : ℕ} (S : Set (ℝ^d)) : Prop :=
  ∀ K : ConvexBody (ℝ^d), volume (K : Set (ℝ^d)) = 1 → (S ∩ K).Nonempty

/-- A set `S ⊆ ℝ^d` has *bounded density*, i.e. growth rate `O(r ^ d)`: there is a constant `C`
such that, for every `r ≥ 1`, the closed ball of radius `r` about the origin contains only
finitely many points of `S`, and at most `C * r ^ d` of them. Equivalently,
$\limsup_{r \to \infty} \#(S \cap B(0, r)) / r^d < \infty$.

The finiteness condition is needed because `Set.ncard` of an infinite set is `0`. -/
def HasBoundedDensity {d : ℕ} (S : Set (ℝ^d)) : Prop :=
  ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
    (S ∩ closedBall 0 r).Finite ∧ (S ∩ closedBall 0 r).ncard ≤ C * r ^ d

/-- A set `S ⊆ ℝ^d` is *uniformly discrete* if there is `r > 0` such that any two distinct
points of `S` are at distance at least `r`. -/
def IsUniformlyDiscrete {d : ℕ} (S : Set (ℝ^d)) : Prop :=
  ∃ r : ℝ, 0 < r ∧ S.Pairwise (fun x y => r ≤ dist x y)

/-- The whole space is a Danzer set. -/
@[category test, AMS 52]
theorem isDanzerSet_univ (d : ℕ) : IsDanzerSet (Set.univ : Set (ℝ^d)) := fun K _ => by
  simpa using K.nonempty

/-- The empty set is not a Danzer set, since the unit cube $[0,1]^d$ has volume one. -/
@[category test, AMS 52]
theorem not_isDanzerSet_empty (d : ℕ) : ¬ IsDanzerSet (∅ : Set (ℝ^d)) := by
  intro h
  let e := PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin d => ℝ
  refine (h ⟨e ⁻¹' Set.Icc 0 1, (convex_Icc _ _).linear_preimage (e : ℝ^d →ₗ[ℝ] Fin d → ℝ),
    e.toHomeomorph.isCompact_preimage.mpr isCompact_Icc, ⟨0, by simp⟩⟩ ?_).ne_empty (by simp)
  rw [ConvexBody.coe_mk, PiLp.coe_continuousLinearEquiv,
    (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage measurableSet_Icc.nullMeasurableSet,
    Real.volume_Icc_pi]
  simp

/-- The whole space `ℝ^d` (for `d ≥ 1`) does not have bounded density: the unit ball contains
infinitely many of its points. -/
@[category test, AMS 52]
theorem not_hasBoundedDensity_univ {d : ℕ} (hd : 0 < d) :
    ¬ HasBoundedDensity (Set.univ : Set (ℝ^d)) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rintro ⟨C, hC⟩
  have h1 := (hC 1 le_rfl).1.measure_zero (volume : Measure (ℝ^d))
  have h2 := measure_closedBall_pos (volume : Measure (ℝ^d)) (0 : ℝ^d) one_pos
  simp at h1
  exact h2.ne' h1

/-- A finite set has bounded density. -/
@[category test, AMS 52]
theorem HasBoundedDensity.of_finite {d : ℕ} {S : Set (ℝ^d)} (hS : S.Finite) :
    HasBoundedDensity S := by
  refine ⟨S.ncard, fun r hr => ⟨hS.subset Set.inter_subset_left, ?_⟩⟩
  calc ((S ∩ closedBall 0 r).ncard : ℝ) ≤ S.ncard := by
        exact_mod_cast Set.ncard_le_ncard Set.inter_subset_left hS
    _ = S.ncard * 1 := (mul_one _).symm
    _ ≤ S.ncard * r ^ d := by gcongr; exact one_le_pow₀ hr

/-- The empty set is uniformly discrete. -/
@[category test, AMS 52]
theorem isUniformlyDiscrete_empty (d : ℕ) : IsUniformlyDiscrete (∅ : Set (ℝ^d)) :=
  ⟨1, one_pos, Set.pairwise_empty _⟩

/--
**Danzer's problem.** Let $d \ge 2$. Does there exist a Danzer set in $\mathbb{R}^d$, i.e. a
set $S \subseteq \mathbb{R}^d$ meeting every convex body of volume $1$, of bounded density,
i.e. with $\#(S \cap B(0, r)) = O(r^d)$?

The answer is unknown and may in principle depend on the dimension $d$, so it is recorded as a
predicate on $d$. The case $d = 1$ is excluded because it is trivial (the integers form a Danzer
set of bounded density in $\mathbb{R}$). By scaling, requiring volume exactly $1$ is no
restriction: the problem is the same for any fixed positive volume.
-/
@[category research open, AMS 52]
theorem danzer_set.parts.i (d : ℕ) (hd : 2 ≤ d) :
    (answer(sorry) : ℕ → Prop) d ↔
      ∃ S : Set (ℝ^d), IsDanzerSet S ∧ HasBoundedDensity S := by
  sorry

/--
**Conway's dead fly problem** (also due to Boshernitzan). Let $d \ge 2$. Does there exist a
uniformly discrete Danzer set in $\mathbb{R}^d$, i.e. a set $S \subseteq \mathbb{R}^d$ meeting
every convex body of volume $1$ such that, for some $r > 0$, any two distinct points of $S$ are
at distance at least $r$?

Conway asked this for the plane $d = 2$; Boshernitzan independently asked it in general
dimension. Such a set is automatically a Delone set of growth rate $O(r^d)$, so a positive answer
would also give a positive answer to Danzer's problem in the same dimension. The answer may in
principle depend on the dimension $d$, so it is recorded as a predicate on $d$.
-/
@[category research open, AMS 52]
theorem danzer_set.parts.ii (d : ℕ) (hd : 2 ≤ d) :
    (answer(sorry) : ℕ → Prop) d ↔
      ∃ S : Set (ℝ^d), IsDanzerSet S ∧ IsUniformlyDiscrete S := by
  sorry

end DanzerSet
