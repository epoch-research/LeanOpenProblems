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
# Apex graphs and Jørgensen's conjecture

*References:*
- [Wikipedia, Apex graph](https://en.wikipedia.org/wiki/apex_graph)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Jø94] Jørgensen, L. K., *Contractions to $K_8$*. J. Graph Theory 18 (1994), 431–448.
- [KNTW12] Kawarabayashi, K., Norine, S., Thomas, R., Wollan, P.,
  *$K_6$ minors in large 6-connected graphs*. [arXiv:1203.2192](https://arxiv.org/abs/1203.2192)

An *apex graph* is a graph that can be made planar by the removal of a single vertex.
Jørgensen conjectured that every $6$-connected graph with no $K_6$ minor is an apex graph.
Kawarabayashi, Norine, Thomas and Wollan proved the conjecture for all sufficiently large
graphs, so a false conjecture would have only finitely many counterexamples.

Mathlib has neither planarity nor graph minors, so this file defines both. Planarity is defined
by a drawing in the plane without crossings, and a minor is defined by branch sets.
-/

namespace ApexGraph

open SimpleGraph unitInterval
open scoped EuclideanGeometry

variable {V W : Type*}

/-- A graph `G` is *planar* if it has a drawing in the plane $\mathbb{R}^2$: the vertices are
sent to distinct points and each edge is sent to an arc (an injective continuous image of the unit
interval) joining the images of its two ends. The interior of an arc contains no vertex, and the
interior of an arc meets no other arc. Two distinct arcs thus meet only in common endpoints.

By Wagner's theorem a finite graph is planar in this sense exactly when it has neither $K_5$
nor $K_{3,3}$ as a minor. -/
def IsPlanar (G : SimpleGraph V) : Prop :=
  ∃ (f : V → ℝ²) (γ : G.edgeSet → I → ℝ²),
    Function.Injective f ∧
    (∀ e, Continuous (γ e) ∧ Function.Injective (γ e)) ∧
    (∀ e : G.edgeSet, s(γ e 0, γ e 1) = (e : Sym2 V).map f) ∧
    (∀ e, ∀ t, t ≠ 0 → t ≠ 1 → γ e t ∉ Set.range f) ∧
    (∀ e e', e ≠ e' → ∀ t t', t ≠ 0 → t ≠ 1 → γ e t ≠ γ e' t')

/-- A graph `G` is an *apex graph* if it has a vertex `v` whose deletion leaves a planar graph.
Such a vertex is called an *apex* of `G`.

Wikipedia also counts the null graph (no vertices) as an apex graph. This definition does not,
but the two agree on every graph with a vertex, and in particular on every $6$-connected graph. -/
def IsApex (G : SimpleGraph V) : Prop :=
  ∃ v : V, IsPlanar (G.induce {v}ᶜ)

/-- The graph `H` is a *minor* of the graph `G` if `H` can be obtained from a subgraph of `G` by
contracting edges. Equivalently, and this is the form used here, there are *branch sets*
`B w ⊆ V(G)` for `w ∈ V(H)` which are pairwise disjoint and each induce a connected (hence
nonempty) subgraph of `G`, such that for every edge `w w'` of `H` some edge of `G` joins `B w`
to `B w'`. -/
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ B : W → Set V, (∀ w, (G.induce (B w)).Connected) ∧
    Pairwise (fun w w' ↦ Disjoint (B w) (B w')) ∧
    ∀ w w', H.Adj w w' → ∃ u ∈ B w, ∃ v ∈ B w', G.Adj u v

/-- **Jørgensen's conjecture** [Jø94]. Every $6$-connected graph with no $K_6$ minor is an apex
graph. That is, if a finite graph $G$ has more than $6$ vertices, stays connected after the
deletion of any set of fewer than $6$ vertices, and does not contain the complete graph $K_6$ as
a minor, then $G$ has a vertex whose deletion leaves a planar graph.

Kawarabayashi, Norine, Thomas and Wollan [KNTW12] proved the conjecture for all sufficiently
large graphs, so a false conjecture would have only finitely many counterexamples. -/
@[category research open, AMS 5]
theorem apex_graph [Fintype V] (G : SimpleGraph V) (h₆ : IsKConnected G 6)
    (hK₆ : ¬ IsMinor (completeGraph (Fin 6)) G) : IsApex G := by
  sorry

/-- A graph with no vertices is planar. -/
@[category test, AMS 5]
theorem isPlanar_of_isEmpty [IsEmpty V] (G : SimpleGraph V) : IsPlanar G := by
  have : IsEmpty G.edgeSet := ⟨fun e ↦ isEmptyElim (Quot.out e.1).1⟩
  exact ⟨isEmptyElim, isEmptyElim, Function.injective_of_subsingleton _,
    isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim⟩

/-- The only edge of the complete graph on two vertices is `s(0, 1)`. -/
@[category API, AMS 5]
private lemma coe_edgeSet_completeGraph_fin_two (e : (completeGraph (Fin 2)).edgeSet) :
    (e : Sym2 (Fin 2)) = s(0, 1) := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h a b =>
    simp only [completeGraph, mem_edgeSet, top_adj] at he
    fin_cases a <;> fin_cases b <;> simp_all [Sym2.eq_swap]

/-- A single edge is planar: draw it as the segment from `0` to `p` for a nonzero vector `p`. -/
@[category test, AMS 5]
theorem isPlanar_completeGraph_fin_two : IsPlanar (completeGraph (Fin 2)) := by
  set p : ℝ² := EuclideanSpace.single 0 1 with hp
  have hp0 : p ≠ 0 := fun h ↦ by simpa [hp] using congrArg (· 0) h
  have hinj : Function.Injective fun r : ℝ ↦ r • p := smul_left_injective ℝ hp0
  have hsub : Subsingleton (completeGraph (Fin 2)).edgeSet :=
    ⟨fun e e' ↦ Subtype.ext ((coe_edgeSet_completeGraph_fin_two e).trans
      (coe_edgeSet_completeGraph_fin_two e').symm)⟩
  refine ⟨fun i ↦ (i : ℝ) • p, fun _ t ↦ (t : ℝ) • p, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j h
    exact Fin.ext (Nat.cast_injective (hinj h))
  · intro e
    exact ⟨by fun_prop, fun s t h ↦ Subtype.ext (hinj h)⟩
  · intro e
    rw [coe_edgeSet_completeGraph_fin_two e]
    simp
  · rintro e t ht0 ht1 ⟨i, hi⟩
    have := hinj hi
    fin_cases i
    · exact ht0 (Subtype.ext (by simpa using this.symm))
    · exact ht1 (Subtype.ext (by simpa using this.symm))
  · intro e e' h
    exact absurd (Subsingleton.elim e e') h

/-- A graph with exactly one vertex is an apex graph. -/
@[category test, AMS 5]
theorem isApex_of_unique [Unique V] (G : SimpleGraph V) : IsApex G :=
  haveI : IsEmpty ({default}ᶜ : Set V) :=
    ⟨fun ⟨v, hv⟩ ↦ hv (Set.mem_singleton_iff.mpr (Subsingleton.elim v default))⟩
  ⟨default, isPlanar_of_isEmpty _⟩

/-- Every graph is a minor of itself. -/
@[category API, AMS 5]
theorem isMinor_refl (G : SimpleGraph V) : IsMinor G G :=
  ⟨fun v ↦ {v}, fun v ↦ by simp,
    fun _ _ h ↦ Set.disjoint_singleton.mpr h,
    fun u v h ↦ ⟨u, rfl, v, rfl, h⟩⟩

/-- A minor of a finite graph has at most as many vertices as the graph. -/
@[category API, AMS 5]
theorem IsMinor.card_le [Fintype V] [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    (h : IsMinor H G) : Fintype.card W ≤ Fintype.card V := by
  obtain ⟨B, hconn, hdisj, -⟩ := h
  refine Fintype.card_le_of_injective (fun x ↦ ((hconn x).nonempty.some : V)) fun x y hxy ↦ ?_
  by_contra hne
  exact (hdisj hne).ne_of_mem (hconn x).nonempty.some.2 (hconn y).nonempty.some.2 hxy

/-- A graph with fewer than `6` vertices has no `K₆` minor. -/
@[category test, AMS 5]
theorem not_isMinor_completeGraph_six [Fintype V] {G : SimpleGraph V} (hV : Fintype.card V < 6) :
    ¬ IsMinor (completeGraph (Fin 6)) G := fun h ↦ by
  have := h.card_le
  simp only [Fintype.card_fin] at this
  omega

/-- The complete graph $K_6$ is a minor of $K_7$. -/
@[category test, AMS 5]
theorem isMinor_completeGraph_six_completeGraph_seven :
    IsMinor (completeGraph (Fin 6)) (completeGraph (Fin 7)) :=
  ⟨fun w ↦ {Fin.castSucc w}, fun w ↦ by simp,
    fun _ _ h ↦ Set.disjoint_singleton.mpr ((Fin.castSucc_injective _).ne h),
    fun u v h ↦ ⟨_, rfl, _, rfl, by simpa using h⟩⟩

end ApexGraph
