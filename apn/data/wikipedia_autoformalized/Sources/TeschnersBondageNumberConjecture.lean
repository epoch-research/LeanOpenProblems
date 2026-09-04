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
# Teschner's bondage number conjecture

The *bondage number* $b(G)$ of a nonempty finite simple graph $G$ (a graph with at least one
edge) is the minimum number of edges whose removal from $G$ strictly increases the domination
number $\gamma(G)$:
$$b(G) = \min\{|B| : B \subseteq E(G),\ \gamma(G - B) > \gamma(G)\}.$$

Fink, Jacobson, Kinch and Roberts (1990) conjectured that $b(G) \le \Delta(G) + 1$, where
$\Delta(G)$ is the maximum degree of $G$. Teschner disproved this with $K_3 \square K_3$, and
Hartnell–Rall and Teschner showed that
$b(K_n \square K_n) = 3(n-1) = \frac32 \Delta(K_n \square K_n)$ for $n \ge 3$.
Teschner (1995) then conjectured that $b(G) \le \frac{3}{2}\Delta(G)$ for every
graph $G$. This conjecture is open.

*References:*
- [Wikipedia, Bondage number](https://en.wikipedia.org/wiki/bondage_number)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Xu12] Jun-Ming Xu, *On Bondage Numbers of Graphs: A Survey with Some Comments*,
  [arXiv:1204.4010](https://arxiv.org/abs/1204.4010), Conjecture 3.6.3.
- [Tes95] Ulrich Teschner, *A new upper bound for the bondage number of graphs with small
  domination number*, Australas. J. Combin. 12 (1995), 27–35.
-/

namespace TeschnersBondageNumberConjecture

open SimpleGraph

variable {V : Type*}

/-- A finite set `B` of edges of `G` is a *bondage set* of `G` if removing the edges in `B`
from `G` strictly increases the domination number. -/
def IsBondageSet (G : SimpleGraph V) (B : Finset (Sym2 V)) : Prop :=
  ↑B ⊆ G.edgeSet ∧ G.dominationNumber < (G.deleteEdges ↑B).dominationNumber

/-- The *bondage number* `b(G)` of a graph `G` is the minimum size of a bondage set of `G`,
that is, the minimum number of edges whose removal strictly increases the domination number.

If `G` has no edges then no bondage set exists and, by the convention `sInf ∅ = 0`,
this returns `0`; the literature leaves `b(G)` undefined (or infinite) in that case. -/
noncomputable def bondageNumber (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ B : Finset (Sym2 V), IsBondageSet G B ∧ B.card = n}

/-- The empty set is never a bondage set. -/
@[category API, AMS 5]
theorem not_isBondageSet_empty (G : SimpleGraph V) : ¬ IsBondageSet G ∅ := by
  simp [IsBondageSet]

/-- Every bondage set of `G` has at least `b(G)` edges. -/
@[category API, AMS 5]
theorem bondageNumber_le_card {G : SimpleGraph V} {B : Finset (Sym2 V)}
    (hB : IsBondageSet G B) : bondageNumber G ≤ B.card :=
  Nat.sInf_le ⟨B, hB, rfl⟩

/-- `b(G) = 0` exactly when `G` has no bondage set at all. -/
@[category API, AMS 5]
theorem bondageNumber_eq_zero_iff {G : SimpleGraph V} :
    bondageNumber G = 0 ↔ ∀ B, ¬ IsBondageSet G B := by
  rw [bondageNumber, Nat.sInf_eq_zero]
  constructor
  · rintro (⟨B, hB, hB0⟩ | h) B' hB'
    · exact not_isBondageSet_empty G (Finset.card_eq_zero.mp hB0 ▸ hB)
    · exact Set.eq_empty_iff_forall_notMem.mp h _ ⟨B', hB', rfl⟩
  · intro h
    exact Or.inr (Set.eq_empty_iff_forall_notMem.mpr fun n ⟨B, hB, _⟩ => h B hB)

/-- Removing all edges of a nonempty finite graph strictly increases the domination number,
so the edge set of a nonempty finite graph is a bondage set. -/
@[category API, AMS 5]
theorem isBondageSet_edgeFinset [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hG : G.edgeSet.Nonempty) : IsBondageSet G G.edgeFinset := by
  refine ⟨by simp, ?_⟩
  have h1 : G.deleteEdges ↑G.edgeFinset = ⊥ := by simp
  rw [h1]
  obtain ⟨e, he⟩ := hG
  induction e with | h u v
  rw [mem_edgeSet] at he
  calc G.dominationNumber ≤ (Finset.univ.erase u).card := by
        refine Nat.sInf_le ⟨Finset.univ.erase u, ?_, rfl⟩
        intro w
        by_cases hw : w = u
        · exact Or.inr ⟨v, by simp [he.ne.symm], hw ▸ he⟩
        · exact Or.inl (by simp [hw])
    _ < Fintype.card V := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
        exact Nat.sub_lt (Fintype.card_pos_iff.mpr ⟨u⟩) Nat.one_pos
    _ ≤ (⊥ : SimpleGraph V).dominationNumber := by
        refine le_csInf ⟨_, Finset.univ, fun w => Or.inl (Finset.mem_univ w), rfl⟩ ?_
        rintro n ⟨D, hD, rfl⟩
        rw [← Finset.card_univ]
        refine Finset.card_le_card fun w _ => ?_
        rcases hD w with h | ⟨_, _, h⟩
        · exact h
        · exact absurd h (by simp)

/-- The bondage number of a nonempty finite graph is well defined and positive. -/
@[category API, AMS 5]
theorem one_le_bondageNumber [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hG : G.edgeSet.Nonempty) : 1 ≤ bondageNumber G := by
  rw [Nat.one_le_iff_ne_zero, Ne, bondageNumber_eq_zero_iff, not_forall]
  exact ⟨_, not_not.mpr (isBondageSet_edgeFinset hG)⟩

/-- The bondage number of the complete graph `K₂` is `1`. -/
@[category test, AMS 5]
theorem bondageNumber_top_fin_two : bondageNumber (⊤ : SimpleGraph (Fin 2)) = 1 := by
  refine le_antisymm ?_ (one_le_bondageNumber ⟨s(0, 1), by decide⟩)
  refine (bondageNumber_le_card (B := {s(0, 1)}) ?_).trans (by simp)
  refine ⟨by simp, ?_⟩
  rw [dom_num_eq_computable, dom_num_eq_computable]
  decide +native

/-- Removing the two edges at a vertex of `K₃` isolates that vertex and increases the
domination number from `1` to `2`. -/
@[category test, AMS 5]
theorem isBondageSet_top_fin_three :
    IsBondageSet (⊤ : SimpleGraph (Fin 3)) {s(0, 1), s(0, 2)} := by
  refine ⟨?_, ?_⟩
  · simp only [Finset.coe_insert, Finset.coe_singleton, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    decide
  · rw [dom_num_eq_computable, dom_num_eq_computable]
    decide +native

/-- The bondage number of the complete graph `K₃` is `2 = ⌈3/2⌉`: removing a single edge
from `K₃` leaves a path, which still has domination number `1`. -/
@[category test, AMS 5]
theorem bondageNumber_top_fin_three : bondageNumber (⊤ : SimpleGraph (Fin 3)) = 2 := by
  refine le_antisymm ((bondageNumber_le_card isBondageSet_top_fin_three).trans (by decide)) ?_
  refine le_csInf ⟨_, _, isBondageSet_top_fin_three, rfl⟩ ?_
  rintro n ⟨B, hB, rfl⟩
  by_contra h
  rcases Nat.lt_succ_iff_lt_or_eq.mp (not_le.mp h) with h0 | h1
  · exact not_isBondageSet_empty _ (Finset.card_eq_zero.mp (Nat.lt_one_iff.mp h0) ▸ hB)
  · obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp h1
    have key : ∀ e : Sym2 (Fin 3), ¬ (⊤ : SimpleGraph (Fin 3)).computable_dom_num <
        ((⊤ : SimpleGraph (Fin 3)).deleteEdges
          (({e} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))).computable_dom_num := by
      decide +native
    have := hB.2
    rw [dom_num_eq_computable, dom_num_eq_computable] at this
    exact key e this

/--
**Teschner's bondage number conjecture** (Teschner 1995; Conjecture 3.6.3 in [Xu12]).

Is the bondage number of a graph always less than or equal to $\frac{3}{2}$ times its maximum
degree? That is, does every finite simple graph $G$ with at least one edge satisfy
$$b(G) \le \tfrac{3}{2}\,\Delta(G)?$$

The graph is required to have at least one edge because the bondage number is only defined for
nonempty graphs. The bound is known to be sharp:
$b(K_n \square K_n) = \frac32 \Delta(K_n \square K_n)$ for $n \ge 3$.
-/
@[category research open, AMS 5]
theorem teschners_bondage_number_conjecture :
    answer(sorry) ↔ ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.edgeSet.Nonempty →
      (bondageNumber G : ℚ) ≤ 3 / 2 * G.maxDegree := by
  sorry

end TeschnersBondageNumberConjecture
