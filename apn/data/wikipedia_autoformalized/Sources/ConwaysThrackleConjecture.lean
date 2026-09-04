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
# Conway's thrackle conjecture

A *thrackle* is a drawing of a finite simple graph in the plane in which the vertices are
distinct points, each edge is a Jordan arc (a simple continuous curve) joining the points of its
two endpoints and passing through no other vertex, and every pair of distinct edges meets exactly
once: two edges sharing an endpoint meet only at that common endpoint, and two edges with no
common endpoint meet at exactly one point of their interiors, where they must cross properly
(transversally), i.e. one curve passes from one side of the other curve to its other side.

John H. Conway conjectured that every thrackle has at most as many edges as vertices.

*References:*
- [Wikipedia, Conway's thrackle conjecture](https://en.wikipedia.org/wiki/Conway%27s_thrackle_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [LPS97] Lovász, L., Pach, J., Szegedy, M., _On Conway's thrackle conjecture_.
  Discrete Comput. Geom. 18 (1997), 369–376.
- [FP11] Fulek, R., Pach, J., _A computational approach to Conway's thrackle conjecture_.
  Comput. Geom. 44 (2011), 345–355. [arXiv:1002.3904](https://arxiv.org/abs/1002.3904)
- [FP19] Fulek, R., Pach, J., _Thrackles: An improved upper bound_.
  Discrete Appl. Math. 259 (2019), 226–231. [arXiv:1708.08037](https://arxiv.org/abs/1708.08037)
-/

namespace ConwaysThrackleConjecture

open Topology
open scoped unitInterval EuclideanGeometry

/--
The curve `δ : I → ℝ²` **crosses** the curve `γ : I → ℝ²` at the interior parameter `s₀` if
the point `δ s₀` lies on `γ` and, in some neighbourhood `U` of `δ s₀`, the points of `δ` just
before `s₀` and just after `s₀` lie on different sides of `γ`: they cannot be joined by a path
inside `U` that avoids `γ`. This is the informal condition that `δ` passes from one side of `γ`
to its other side at `δ s₀`, as opposed to touching `γ` tangentially.
-/
def CrossesAt (γ δ : I → ℝ²) (s₀ : I) : Prop :=
  0 < s₀ ∧ s₀ < 1 ∧ δ s₀ ∈ Set.range γ ∧
    ∃ U ∈ 𝓝 (δ s₀), ∀ᶠ s in 𝓝[<] s₀, ∀ᶠ s' in 𝓝[>] s₀,
      ¬ JoinedIn (U \ Set.range γ) (δ s) (δ s')

/--
Two curves `γ δ : I → ℝ²` have a **proper crossing** at the point `p` if `p` is an interior
point of both curves and each curve crosses the other at `p`, i.e. the four half-curves emanating
from `p` alternate around `p`. This is the transversality condition in the definition of a
thrackle.
-/
def IsProperCrossing (γ δ : I → ℝ²) (p : ℝ²) : Prop :=
  ∃ t₀ s₀ : I, γ t₀ = p ∧ δ s₀ = p ∧ CrossesAt γ δ s₀ ∧ CrossesAt δ γ t₀

/--
A **thrackle drawing** of a simple graph `G` in the plane consists of a point `vertex v` for each
vertex `v` and a curve `arc e : I → ℝ²` for each edge `e` such that:
- distinct vertices are drawn as distinct points;
- each edge is drawn as a Jordan arc (a continuous injective curve) whose two endpoints are the
  points representing the two ends of the edge;
- no arc passes through a vertex other than its endpoints;
- every two distinct edges meet in exactly one point (so two edges with a common endpoint
  meet only at that endpoint);
- two edges with no common endpoint cross properly (transversally) at their meeting point.
-/
structure IsThrackleDrawing {V : Type*} (G : SimpleGraph V) (vertex : V → ℝ²)
    (arc : G.edgeSet → I → ℝ²) : Prop where
  vertex_injective : Function.Injective vertex
  continuous : ∀ e, Continuous (arc e)
  arc_injective : ∀ e, Function.Injective (arc e)
  endpoints : ∀ e, s(arc e 0, arc e 1) = (e : Sym2 V).map vertex
  avoids_vertices : ∀ e v, vertex v ∈ Set.range (arc e) → v ∈ (e : Sym2 V)
  meet_once : ∀ e e' : G.edgeSet, e ≠ e' →
    ∃ p, Set.range (arc e) ∩ Set.range (arc e') = {p}
  cross : ∀ e e' : G.edgeSet, (∀ v, v ∈ (e : Sym2 V) → v ∉ (e' : Sym2 V)) →
    ∀ p ∈ Set.range (arc e) ∩ Set.range (arc e'), IsProperCrossing (arc e) (arc e') p

/--
**Conway's thrackle conjecture.** Thrackles cannot have more edges than vertices: if a finite
simple graph $G$ admits a thrackle drawing in the plane, then $|E(G)| \le |V(G)|$.
-/
@[category research open, AMS 5 52]
theorem conways_thrackle_conjecture {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (vertex : V → ℝ²) (arc : G.edgeSet → I → ℝ²)
    (h : IsThrackleDrawing G vertex arc) :
    G.edgeFinset.card ≤ Fintype.card V := by
  sorry

/-- The straight segment on the coordinate axis `i` from `-1` to `1`, parametrised by `I`. -/
noncomputable def axisSegment (i : Fin 2) (t : I) : ℝ² :=
  (2 * (t : ℝ) - 1) • EuclideanSpace.single i 1

/-- The coordinates of a point on `axisSegment i`. -/
@[category API, AMS 5 52]
lemma axisSegment_apply (i k : Fin 2) (t : I) :
    axisSegment i t k = if k = i then 2 * (t : ℝ) - 1 else 0 := by
  simp [axisSegment]

/-- The parametrisation `axisSegment i` is injective. -/
@[category API, AMS 5 52]
lemma axisSegment_injective (i : Fin 2) : Function.Injective (axisSegment i) := fun t t' h => by
  have := congrArg (· i) h
  simp only [axisSegment_apply, if_true] at this
  ext
  linarith

/-- The segment on the `j`-axis crosses the segment on the `i`-axis (`i ≠ j`) at the origin. -/
@[category API, AMS 5 52]
lemma crossesAt_axisSegment {i j : Fin 2} (hij : i ≠ j) :
    CrossesAt (axisSegment i) (axisSegment j) ⟨1 / 2, by norm_num⟩ := by
  refine ⟨by rw [← Subtype.coe_lt_coe]; norm_num, by rw [← Subtype.coe_lt_coe]; norm_num,
    ⟨⟨1 / 2, by norm_num⟩, by simp [axisSegment]⟩, {q | q i ∈ Set.Ioo (-1) 1}, ?_, ?_⟩
  · exact (isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous).mem_nhds
      (by simp [axisSegment])
  · refine eventually_nhdsWithin_of_forall fun s hs =>
      eventually_nhdsWithin_of_forall fun s' hs' ⟨p, hp⟩ => ?_
    have hs : (s : ℝ) < 1 / 2 := hs
    have hs' : (1 / 2 : ℝ) < s' := hs'
    have hcont : Continuous fun t => (p t) j :=
      (EuclideanSpace.proj j).continuous.comp p.continuous
    have h0 : (p 0) j = 2 * (s : ℝ) - 1 := by simp [axisSegment_apply]
    have h1 : (p 1) j = 2 * (s' : ℝ) - 1 := by simp [axisSegment_apply]
    have hmem : (0 : ℝ) ∈ Set.Icc ((p 0) j) ((p 1) j) :=
      ⟨by rw [h0]; linarith, by rw [h1]; linarith⟩
    obtain ⟨t, ht⟩ := intermediate_value_univ 0 1 hcont hmem
    obtain ⟨hU, hγ⟩ := hp t
    refine hγ ⟨⟨((p t) i + 1) / 2, ?_⟩, ?_⟩
    · exact ⟨by linarith [hU.1], by linarith [hU.2]⟩
    · ext k
      rw [axisSegment_apply]
      by_cases hk : k = i
      · subst hk; simp; ring
      · have : k = j := by omega
        subst this
        simp [hij.symm, ht]

/-- The two coordinate axes cross properly at the origin. -/
@[category test, AMS 5 52]
theorem isProperCrossing_axisSegment : IsProperCrossing (axisSegment 0) (axisSegment 1) 0 :=
  ⟨⟨1 / 2, by norm_num⟩, ⟨1 / 2, by norm_num⟩, by simp [axisSegment], by simp [axisSegment],
    crossesAt_axisSegment (by decide), crossesAt_axisSegment (by decide)⟩

/-- The "V"-shaped curve `s ↦ (2s - 1, |2s - 1|)`. It touches the horizontal axis at the origin
from above without crossing it. -/
noncomputable def touchingCurve (s : I) : ℝ² :=
  (2 * (s : ℝ) - 1) • EuclideanSpace.single 0 1 +
    |2 * (s : ℝ) - 1| • EuclideanSpace.single 1 1

/-- The second coordinate of `touchingCurve s` is `|2s - 1|`. -/
@[category API, AMS 5 52]
lemma touchingCurve_apply_one (s : I) : touchingCurve s 1 = |2 * (s : ℝ) - 1| := by
  simp [touchingCurve]

/-- A curve that only touches another curve tangentially does not cross it. -/
@[category test, AMS 5 52]
theorem not_crossesAt_touchingCurve :
    ¬ CrossesAt (axisSegment 0) touchingCurve ⟨1 / 2, by norm_num⟩ := by
  rintro ⟨-, -, -, U, hU, hev⟩
  have h0 : touchingCurve ⟨1 / 2, by norm_num⟩ = 0 := by simp [touchingCurve]
  rw [h0] at hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hcont : Continuous touchingCurve := by unfold touchingCurve; fun_prop
  have hev' : ∀ᶠ s in 𝓝 (⟨1 / 2, by norm_num⟩ : I), touchingCurve s ∈ Metric.ball 0 ε := by
    have := hcont.continuousAt (x := ⟨1 / 2, by norm_num⟩)
    rw [ContinuousAt, h0] at this
    exact this (Metric.ball_mem_nhds 0 hε)
  haveI : (𝓝[<] (⟨1 / 2, by norm_num⟩ : I)).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, by rw [← Subtype.coe_lt_coe]; norm_num⟩
  haveI : (𝓝[>] (⟨1 / 2, by norm_num⟩ : I)).NeBot :=
    nhdsGT_neBot_of_exists_gt ⟨1, by rw [← Subtype.coe_lt_coe]; norm_num⟩
  obtain ⟨s, hs, hsε, hs₁⟩ :=
    (hev.and ((hev'.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin)).exists
  obtain ⟨s', hJ, hs'ε, hs'₁⟩ :=
    (hs.and ((hev'.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin)).exists
  apply hJ
  have hpos : ∀ x : I, x ≠ ⟨1 / 2, by norm_num⟩ → 0 < touchingCurve x 1 := fun x hx => by
    rw [touchingCurve_apply_one, abs_pos, sub_ne_zero]
    intro h
    apply hx
    ext
    linarith
  set S : Set ℝ² := Metric.ball 0 ε ∩ {q | 0 < q 1}
  have hS : Convex ℝ S :=
    (convex_ball 0 ε).inter
      ((convex_Ioi (0 : ℝ)).linear_preimage (EuclideanSpace.proj 1).toLinearMap)
  have hδs : touchingCurve s ∈ S := ⟨hsε, hpos s (ne_of_lt hs₁)⟩
  have hδs' : touchingCurve s' ∈ S := ⟨hs'ε, hpos s' (ne_of_gt hs'₁)⟩
  refine ((hS.isPathConnected ⟨_, hδs⟩).joinedIn _ hδs _ hδs').mono ?_
  rintro q ⟨hq₁, hq₂⟩
  refine ⟨hball hq₁, ?_⟩
  rintro ⟨t, ht⟩
  have := congrArg (· 1) ht
  simp only [axisSegment_apply] at this
  simp at this
  simp only [Set.mem_setOf_eq] at hq₂
  linarith

/-- The graph with a single edge, drawn as a straight segment, is a thrackle. -/
@[category test, AMS 5 52]
theorem isThrackleDrawing_single_edge :
    IsThrackleDrawing (⊤ : SimpleGraph (Fin 2)) ![axisSegment 0 0, axisSegment 0 1]
      fun _ => axisSegment 0 := by
  have hedge : ∀ e : (⊤ : SimpleGraph (Fin 2)).edgeSet, (e : Sym2 (Fin 2)) = s(0, 1) := by
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | hf a b =>
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at he
      fin_cases a <;> fin_cases b <;> simp_all [Sym2.eq_swap]
  refine ⟨?_, fun _ => by unfold axisSegment; fun_prop, fun _ => axisSegment_injective 0, ?_, ?_,
    ?_, ?_⟩
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [(axisSegment_injective 0).eq_iff]
  · intro e
    rw [hedge e]
    simp
  · intro e v _
    rw [hedge e]
    fin_cases v <;> simp
  · intro e e' hne
    exact absurd (Subtype.ext ((hedge e).trans (hedge e').symm)) hne
  · intro e e' h
    exact absurd (by rw [hedge e']; simp) (h 0 (by rw [hedge e]; simp))

end ConwaysThrackleConjecture
