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
# Petersen graph: Tutte's 4-flow conjecture

Tutte's 4-flow conjecture states that every Petersen-minor-free bridgeless graph has a
nowhere-zero 4-flow. Here graphs are finite multigraphs (loops and parallel edges are allowed),
and "Petersen-minor-free" means that the Petersen graph is not a minor of the graph.

*References:*
- [Wikipedia, Petersen graph](https://en.wikipedia.org/wiki/Petersen_graph)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Nowhere-zero flow](https://en.wikipedia.org/wiki/Nowhere-zero_flow)
- [Tu66] Tutte, W. T. *On the algebraic theory of graph colorings*.
  J. Combinatorial Theory 1 (1966), 15–50.
- [Zh97] Zhang, Cun-Quan. *Integer Flows and Cycle Covers of Graphs*. CRC Press (1997).
-/

open scoped Graph

namespace Petersen

variable {α β : Type*}

/-- The Petersen graph, realised as the Kneser graph `KG(5,2)`: the vertices are the 2-element
subsets of a 5-element set, and two vertices are adjacent when the subsets are disjoint. -/
def petersenGraph : SimpleGraph {s : Finset (Fin 5) // s.card = 2} where
  Adj s t := Disjoint s.1 t.1
  symm _ _ h := h.symm
  loopless s h := by
    have hs := s.2
    simp only [disjoint_self, Finset.bot_eq_empty] at h
    simp [h] at hs

instance : DecidableRel petersenGraph.Adj :=
  fun s t => inferInstanceAs (Decidable (Disjoint s.1 t.1))

/-- The Petersen graph has 10 vertices. -/
@[category test, AMS 5]
theorem card_petersenGraph_vertices : Fintype.card {s : Finset (Fin 5) // s.card = 2} = 10 := by
  decide

/-- The Petersen graph has 15 edges. -/
@[category test, AMS 5]
theorem card_petersenGraph_edges : petersenGraph.edgeFinset.card = 15 := by
  decide

/-- The Petersen graph is cubic. -/
@[category test, AMS 5]
theorem petersenGraph_degree (v : {s : Finset (Fin 5) // s.card = 2}) :
    petersenGraph.degree v = 3 := by
  revert v
  decide

/-- An edge `e` of a multigraph `G` is a *bridge* if its ends are not joined by a walk of `G`
avoiding `e`, i.e. deleting `e` disconnects its ends. Loops, edges having a parallel edge, and
elements of `β` that are not edges of `G` are never bridges. -/
def IsBridge (G : Graph α β) (e : β) : Prop :=
  ∃ x y, G.IsLink e x y ∧ ¬ Relation.ReflTransGen (fun a b ↦ ∃ f ≠ e, G.IsLink f a b) x y

/-- A multigraph is *bridgeless* if none of its edges is a bridge. -/
def IsBridgeless (G : Graph α β) : Prop := ∀ e, ¬ IsBridge G e

/-- A finite multigraph `G` has a *nowhere-zero `k`-flow* if there are an orientation of `G`,
given by tail and head maps `t h : E(G) → α` with `G.IsLink e (t e) (h e)` for every edge `e`,
and an integer weighting `φ` of the edges with `0 < |φ e| < k`, that satisfy Kirchhoff's law at
every vertex `v`: the total weight of the edges with tail `v` equals the total weight of the
edges with head `v`. (Sums are `finsum`s, which are the usual finite sums when `E(G)` is
finite.) -/
def HasNowhereZeroFlow (G : Graph α β) (k : ℕ) : Prop :=
  ∃ (t h : E(G) → α) (φ : E(G) → ℤ),
    (∀ e : E(G), G.IsLink e (t e) (h e)) ∧
    (∀ e, 0 < |φ e| ∧ |φ e| < k) ∧
    ∀ v, ∑ᶠ e ∈ {e | t e = v}, φ e = ∑ᶠ e ∈ {e | h e = v}, φ e

/-- A graph with no edges has a nowhere-zero `k`-flow for every `k`. -/
@[category test, AMS 5]
theorem hasNowhereZeroFlow_of_edgeSet_eq_empty (G : Graph α β) (hE : E(G) = ∅) (k : ℕ) :
    HasNowhereZeroFlow G k := by
  have : IsEmpty E(G) := by simp [hE]
  exact ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim, fun v ↦ by simp⟩

/-- The multigraph with two vertices joined by a single edge. -/
def singleEdge : Graph (Fin 2) Unit where
  vertexSet := Set.univ
  IsLink _ x y := x ≠ y
  edgeSet := Set.univ
  isLink_symm _ _ _ _ h := h.symm
  eq_or_eq_of_isLink_of_isLink := by decide
  edge_mem_iff_exists_isLink := by simp
  left_mem_of_isLink := by simp

/-- The edge of `singleEdge` is a bridge. -/
@[category test, AMS 5]
theorem isBridge_singleEdge : IsBridge singleEdge () := by
  refine ⟨0, 1, show (0 : Fin 2) ≠ 1 by decide, fun h ↦ ?_⟩
  rw [Relation.reflTransGen_iff_eq fun _ ⟨_, hf, _⟩ ↦ hf rfl] at h
  exact absurd h (by decide)

/-- `singleEdge` has no nowhere-zero `k`-flow, for any `k`. -/
@[category test, AMS 5]
theorem not_hasNowhereZeroFlow_singleEdge (k : ℕ) : ¬ HasNowhereZeroFlow singleEdge k := by
  rintro ⟨t, h, φ, hlink, hnz, hK⟩
  set e : E(singleEdge) := ⟨(), trivial⟩
  have he : ∀ e' : E(singleEdge), e' = e := fun _ ↦ Subtype.ext rfl
  have h1 : {e' : E(singleEdge) | t e' = t e} = Set.univ := by
    ext e'
    simp [he e']
  have h2 : {e' : E(singleEdge) | h e' = t e} = ∅ := by
    ext e'
    simpa [he e'] using fun heq ↦ hlink e heq.symm
  have key := hK (t e)
  rw [h1, h2, finsum_mem_univ, finsum_mem_empty, finsum_eq_sum_of_fintype,
    show (Finset.univ : Finset E(singleEdge)) = {e} from Finset.ext fun e' ↦ by simp [he e'],
    Finset.sum_singleton] at key
  simpa [key] using (hnz e).1

/-- A simple graph `H` is a *minor* of the multigraph `G` if `G` contains a model of `H`:
pairwise disjoint nonempty sets `B i ⊆ V(G)` of vertices (the *branch sets*, indexed by the
vertices `i` of `H`), each connected in `G`, such that for every edge `ij` of `H` some edge of
`G` joins `B i` to `B j`. This is the standard characterisation of `H` being obtainable from `G`
by deleting vertices and edges and contracting edges. -/
def HasMinor {ι : Type*} (G : Graph α β) (H : SimpleGraph ι) : Prop :=
  ∃ B : ι → Set α,
    (∀ i, B i ⊆ V(G)) ∧
    (∀ i, (B i).Nonempty) ∧
    Pairwise (fun i j ↦ Disjoint (B i) (B j)) ∧
    (∀ i, ∀ x ∈ B i, ∀ y ∈ B i,
      Relation.ReflTransGen (fun a b ↦ a ∈ B i ∧ b ∈ B i ∧ G.Adj a b) x y) ∧
    ∀ i j, H.Adj i j → ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y

/-- The complete graph on two vertices is a minor of `singleEdge`. -/
@[category test, AMS 5]
theorem hasMinor_singleEdge_top : HasMinor singleEdge (⊤ : SimpleGraph (Fin 2)) := by
  refine ⟨fun i ↦ {i}, fun _ ↦ Set.subset_univ _, fun _ ↦ Set.singleton_nonempty _,
    fun i j hij ↦ Set.disjoint_singleton.mpr hij, ?_,
    fun i j hij ↦ ⟨i, rfl, j, rfl, (), hij⟩⟩
  rintro i x rfl y rfl
  exact Relation.ReflTransGen.refl

/-- **Tutte's 4-flow conjecture.** Every Petersen-minor-free bridgeless graph has a nowhere-zero
4-flow. That is, every finite multigraph (loops and parallel edges allowed) with no bridge and
without the Petersen graph as a minor admits an orientation and an edge weighting with values in
$\{\pm 1, \pm 2, \pm 3\}$ satisfying Kirchhoff's law at every vertex. -/
@[category research open, AMS 5]
theorem petersen [Finite α] [Finite β] (G : Graph α β)
    (hG : IsBridgeless G) (hP : ¬ HasMinor G petersenGraph) :
    HasNowhereZeroFlow G 4 := by
  sorry

end Petersen
