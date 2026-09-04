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

/-- The multigraph with two vertices joined by a single edge. -/
def singleEdge : Graph (Fin 2) Unit where
  vertexSet := Set.univ
  IsLink _ x y := x ≠ y
  edgeSet := Set.univ
  isLink_symm _ _ _ _ h := h.symm
  eq_or_eq_of_isLink_of_isLink := by decide
  edge_mem_iff_exists_isLink := by simp
  left_mem_of_isLink := by simp

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

/-- **Tutte's 4-flow conjecture.** Every Petersen-minor-free bridgeless graph has a nowhere-zero
4-flow. That is, every finite multigraph (loops and parallel edges allowed) with no bridge and
without the Petersen graph as a minor admits an orientation and an edge weighting with values in
$\{\pm 1, \pm 2, \pm 3\}$ satisfying Kirchhoff's law at every vertex. -/
theorem petersen [Finite α] [Finite β] (G : Graph α β)
    (hG : IsBridgeless G) (hP : ¬ HasMinor G petersenGraph) :
    HasNowhereZeroFlow G 4 := by
  sorry

end Petersen

theorem Petersen.petersen.disproof : ¬ (type_of% @Petersen.petersen) := sorry
