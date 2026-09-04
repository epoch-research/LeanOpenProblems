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
# Tuza's conjecture

Tuza's conjecture (1981) concerns triangles in finite undirected graphs. For a graph $G$ let
$\nu(G)$ be the *triangle packing number*, the largest number of pairwise edge-disjoint
triangles in $G$, and let $\tau(G)$ be the *triangle hitting number*, the smallest size of a
set of edges meeting every triangle of $G$. Trivially $\nu(G) \le \tau(G) \le 3\nu(G)$.
Tuza conjectured that $\tau(G) \le 2\nu(G)$ for every graph $G$.

*References:*
- [Wikipedia: Tuza's conjecture](https://en.wikipedia.org/wiki/Tuza%27s_conjecture)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- Tuza, Zs. (1981). "Conjecture." In *Finite and Infinite Sets, Proc. Colloq. Math. Soc. János
  Bolyai*, Eger, Hungary, p. 888.
-/

open Finset SimpleGraph

namespace TuzasConjecture

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/--
A finite set `T` of triangles of `G` (a triangle is a `3`-clique, given by its vertex set) is a
*triangle packing* if its triangles are pairwise edge-disjoint, i.e. no edge of `G` lies in two
distinct triangles of `T`.
-/
def IsTrianglePacking (T : Finset (Finset V)) : Prop :=
  T ⊆ G.cliqueFinset 3 ∧
    ∀ s ∈ T, ∀ t ∈ T, s ≠ t → ∀ e ∈ G.edgeFinset, e ∈ s.sym2 → e ∉ t.sym2

/--
The *triangle packing number* $\nu(G)$ of a finite graph $G$: the largest number of pairwise
edge-disjoint triangles in $G$.
-/
noncomputable def trianglePackingNumber : ℕ :=
  sSup {n | ∃ T, IsTrianglePacking G T ∧ T.card = n}

/--
A set `E` of edges of `G` is a *triangle hitting set* if every triangle of `G` contains an edge
of `E`.
-/
def IsTriangleHittingSet (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2

/--
The *triangle hitting number* $\tau(G)$ of a finite graph $G$: the smallest size of a set of edges
of $G$ meeting every triangle of $G$.
-/
noncomputable def triangleHittingNumber : ℕ :=
  sInf {n | ∃ E, IsTriangleHittingSet G E ∧ E.card = n}

/--
**Tuza's conjecture.** Let $G$ be a finite simple undirected graph and let $\nu(G)$ be the
maximum number of pairwise edge-disjoint triangles in $G$. Can all triangles of $G$ be hit by a
set of at most $2\nu(G)$ edges? That is, is there a set of at most $2\nu(G)$ edges of $G$ that
contains an edge of every triangle of $G$?
-/
@[category research open, AMS 5]
theorem tuzas_conjecture : answer(sorry) ↔
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      ∃ E, IsTriangleHittingSet G E ∧ E.card ≤ 2 * trianglePackingNumber G := by
  sorry

/--
**Tuza's conjecture**, in terms of the triangle hitting number: is $\tau(G) \le 2\nu(G)$ for
every finite simple undirected graph $G$?
-/
@[category research open, AMS 5]
theorem tuzas_conjecture.variants.hittingNumber : answer(sorry) ↔
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      triangleHittingNumber G ≤ 2 * trianglePackingNumber G := by
  sorry

/-- The empty set of triangles is a triangle packing. -/
@[category API, AMS 5]
theorem isTrianglePacking_empty : IsTrianglePacking G ∅ := by
  simp [IsTrianglePacking]

/-- A triangle packing has at most as many elements as there are triangles in `G`. -/
@[category API, AMS 5]
theorem IsTrianglePacking.card_le {T : Finset (Finset V)} (hT : IsTrianglePacking G T) :
    T.card ≤ (G.cliqueFinset 3).card :=
  card_le_card hT.1

/-- The set of all edges of `G` is a triangle hitting set. -/
@[category API, AMS 5]
theorem isTriangleHittingSet_edgeFinset : IsTriangleHittingSet G G.edgeFinset := by
  refine ⟨Finset.Subset.refl _, fun t ht => ?_⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.mp (mem_cliqueFinset_iff.mp ht)
  exact ⟨s(a, b), mem_edgeFinset.mpr hab, by simp⟩

/-- A triangle hitting set contains a distinct edge of each triangle of a triangle packing. -/
@[category API, AMS 5]
theorem IsTrianglePacking.card_le_of_isTriangleHittingSet {T : Finset (Finset V)}
    {E : Finset (Sym2 V)} (hT : IsTrianglePacking G T) (hE : IsTriangleHittingSet G E) :
    T.card ≤ E.card := by
  refine card_le_card_of_forall_subsingleton (fun t e => e ∈ t.sym2)
    (fun t ht => hE.2 t (hT.1 ht)) ?_
  intro e he s ⟨hs, hes⟩ t ⟨ht, het⟩
  by_contra hst
  exact hT.2 s hs t ht hst e (hE.1 he) hes het

/-- The trivial lower bound $\nu(G) \le \tau(G)$. -/
@[category textbook, AMS 5]
theorem trianglePackingNumber_le_triangleHittingNumber :
    trianglePackingNumber G ≤ triangleHittingNumber G := by
  refine le_csInf ⟨_, _, isTriangleHittingSet_edgeFinset G, rfl⟩ ?_
  rintro m ⟨E, hE, rfl⟩
  refine csSup_le ⟨0, ∅, isTrianglePacking_empty G, rfl⟩ ?_
  rintro n ⟨T, hT, rfl⟩
  exact hT.card_le_of_isTriangleHittingSet G hE

/-- The trivial upper bound $\tau(G) \le 3\nu(G)$, which Tuza's conjecture proposes to improve. -/
@[category textbook, AMS 5]
theorem triangleHittingNumber_le_three_mul_trianglePackingNumber :
    triangleHittingNumber G ≤ 3 * trianglePackingNumber G := by
  sorry

/-- The edgeless graph has triangle packing number `0`. -/
@[category test, AMS 5]
theorem trianglePackingNumber_bot : trianglePackingNumber (⊥ : SimpleGraph V) = 0 := by
  refine Nat.le_zero.mp (csSup_le ⟨0, ∅, isTrianglePacking_empty _, rfl⟩ ?_)
  rintro n ⟨T, hT, rfl⟩
  have := hT.card_le
  rwa [cliqueFinset_eq_empty_iff.mpr (cliqueFree_bot (by norm_num)), card_empty] at this

/-- The edgeless graph has triangle hitting number `0`. -/
@[category test, AMS 5]
theorem triangleHittingNumber_bot : triangleHittingNumber (⊥ : SimpleGraph V) = 0 :=
  Nat.le_zero.mp <| Nat.sInf_le ⟨∅, ⟨empty_subset _, by simp⟩, rfl⟩

/-- The triangle $K_3$ has triangle packing number `1`. -/
@[category test, AMS 5]
theorem trianglePackingNumber_top_fin_three :
    trianglePackingNumber (⊤ : SimpleGraph (Fin 3)) = 1 := by
  have h : ∀ n ∈ {n | ∃ T, IsTrianglePacking (⊤ : SimpleGraph (Fin 3)) T ∧ T.card = n},
      n ≤ 1 := by
    rintro n ⟨T, hT, rfl⟩
    exact hT.card_le.trans (by decide)
  refine le_antisymm (csSup_le ⟨0, ∅, isTrianglePacking_empty _, rfl⟩ h) ?_
  exact le_csSup ⟨1, h⟩ ⟨{Finset.univ}, by unfold IsTrianglePacking; decide, rfl⟩

/-- The triangle $K_3$ has triangle hitting number `1`. -/
@[category test, AMS 5]
theorem triangleHittingNumber_top_fin_three :
    triangleHittingNumber (⊤ : SimpleGraph (Fin 3)) = 1 := by
  refine le_antisymm (Nat.sInf_le ⟨{s(0, 1)}, by unfold IsTriangleHittingSet; decide, rfl⟩) ?_
  refine le_csInf ⟨_, _, isTriangleHittingSet_edgeFinset _, rfl⟩ ?_
  rintro n ⟨E, hE, rfl⟩
  obtain ⟨e, he, -⟩ := hE.2 Finset.univ (by decide)
  exact card_pos.mpr ⟨e, he⟩

end TuzasConjecture
