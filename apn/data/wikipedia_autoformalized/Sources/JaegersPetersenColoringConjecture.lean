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
# Jaeger's Petersen-coloring conjecture

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Petersen graph: Petersen coloring conjecture](https://en.wikipedia.org/wiki/Petersen_graph%23Petersen_coloring_conjecture)
- [Ja88] Jaeger, F., *Nowhere-zero flow problems*. In: Selected Topics in Graph Theory 3,
  Academic Press (1988), 71--95.

An *Eulerian subgraph* of a graph $G$ is a set of edges of $G$ meeting every vertex of $G$ an
even number of times. These edge sets are the elements of the cycle space of $G$ over
$\mathbb{Z}/2$ and are also called *cycles*. A map from the edges of $G$ to the edges of $H$ is
*cycle-continuous* if the preimage of every cycle of $H$ is a cycle of $G$.

Jaeger's Petersen-coloring conjecture asserts that every bridgeless cubic graph has a
cycle-continuous mapping to the Petersen graph. The Wikipedia article on the Petersen graph
states the conjecture for all bridgeless graphs; that version is known to be equivalent to the
cubic one, which is the form posed by the list entry and formalised here.
-/

open SimpleGraph

namespace JaegersPetersenColoringConjecture

variable {V W : Type*}

/-- The Petersen graph, realised as the Kneser graph $KG(5, 2)$: its vertices are the $10$
two-element subsets of a five-element set, and two of them are adjacent if and only if they are
disjoint. -/
def petersenGraph : SimpleGraph {s : Finset (Fin 5) // s.card = 2} where
  Adj s t := Disjoint s.1 t.1
  symm _ _ h := h.symm
  loopless s h := by
    have hs := s.2
    simp only [Finset.disjoint_self_iff_empty] at h
    simp [h] at hs

instance : DecidableRel petersenGraph.Adj :=
  fun s t => inferInstanceAs (Decidable (Disjoint s.1 t.1))

/-- A set `C` of edges of `G` is an *even subgraph* (an *Eulerian subgraph*, or a *cycle* in the
sense of the cycle space over $\mathbb{Z}/2$) if every vertex of `G` lies on an even number of
edges of `C`. Connectedness is not required. The finiteness assumption on the vertex type makes
`Set.ncard` count the edges of `C` at a vertex correctly. -/
def IsEvenSubgraph [Finite V] (G : SimpleGraph V) (C : Set G.edgeSet) : Prop :=
  ∀ v : V, Even {e ∈ C | v ∈ (e : Sym2 V)}.ncard

/-- A map `f` from the edges of `G` to the edges of `H` is *cycle-continuous* if the preimage
under `f` of every even subgraph (cycle) of `H` is an even subgraph (cycle) of `G`. No
compatibility with the vertices is required: `f` is merely a map between edge sets. -/
def IsCycleContinuous [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G.edgeSet → H.edgeSet) : Prop :=
  ∀ C : Set H.edgeSet, IsEvenSubgraph H C → IsEvenSubgraph G (f ⁻¹' C)

/--
**Jaeger's Petersen-coloring conjecture.** Every bridgeless cubic graph has a cycle-continuous
mapping to the Petersen graph.

Here a *cubic graph* is a finite simple graph in which every vertex has degree $3$
(connectedness is not required), a graph is *bridgeless* if none of its edges is a bridge, and a
map $f \colon E(G) \to E(P)$ to the edge set of the Petersen graph $P$ is *cycle-continuous* if the
preimage under $f$ of every cycle (Eulerian subgraph) of $P$ is a cycle of $G$.
-/
@[category research open, AMS 5]
theorem jaegers_petersen_coloring_conjecture [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : G.IsRegularOfDegree 3) (hbridgeless : G.IsBridgeless) :
    ∃ f : G.edgeSet → petersenGraph.edgeSet, IsCycleContinuous f := by
  sorry

/-- The Petersen graph is the (unique) strongly regular graph with parameters $(10, 3, 0, 1)$: it
has $10$ vertices, is cubic, adjacent vertices have no common neighbour and non-adjacent vertices
have exactly one common neighbour. -/
@[category test, AMS 5]
theorem petersenGraph_isSRGWith : petersenGraph.IsSRGWith 10 3 0 1 where
  card := by
    rw [Fintype.card_finset_len, Fintype.card_fin]
    rfl
  regular := by
    unfold IsRegularOfDegree
    decide
  of_adj := by decide
  of_not_adj := by
    unfold Pairwise
    decide

/-- The Petersen graph has $15$ edges. -/
@[category test, AMS 5]
theorem card_petersenGraph_edgeFinset : petersenGraph.edgeFinset.card = 15 := by
  decide

/-- The Petersen graph is bridgeless. -/
@[category test, AMS 5]
theorem petersenGraph_isBridgeless : petersenGraph.IsBridgeless := by
  intro e he
  induction e using Sym2.ind with
  | h u v =>
    rw [isBridge_iff]
    revert u v
    decide

/-- The empty set of edges is an even subgraph. -/
@[category API, AMS 5]
theorem isEvenSubgraph_empty [Finite V] (G : SimpleGraph V) : IsEvenSubgraph G ∅ := by
  intro v
  simp

/-- The number of edges of `G` at a vertex `v` is the degree of `v`. -/
@[category API, AMS 5]
theorem ncard_univ_incident [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : {e ∈ (Set.univ : Set G.edgeSet) | v ∈ (e : Sym2 V)}.ncard = G.degree v := by
  have h : Subtype.val '' {e ∈ (Set.univ : Set G.edgeSet) | v ∈ (e : Sym2 V)} =
      G.incidenceSet v := by
    ext e
    simp [incidenceSet, and_comm]
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, h, Set.ncard_eq_toFinset_card',
    ← incidenceFinset, card_incidenceFinset_eq_degree]

/-- The whole edge set of `G` is an even subgraph if and only if every vertex has even degree. -/
@[category API, AMS 5]
theorem isEvenSubgraph_univ_iff [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : IsEvenSubgraph G Set.univ ↔ ∀ v, Even (G.degree v) := by
  simp only [IsEvenSubgraph, ncard_univ_incident]

/-- The whole edge set of the Petersen graph is not a cycle, since every vertex has degree $3$. -/
@[category test, AMS 5]
theorem not_isEvenSubgraph_univ_petersenGraph : ¬ IsEvenSubgraph petersenGraph Set.univ := by
  rw [isEvenSubgraph_univ_iff]
  decide

/-- The identity map on the edges of a graph is cycle-continuous. -/
@[category API, AMS 5]
theorem isCycleContinuous_id [Finite V] (G : SimpleGraph V) :
    IsCycleContinuous (id : G.edgeSet → G.edgeSet) :=
  fun _ hC => hC

/-- The composite of two cycle-continuous maps is cycle-continuous. -/
@[category API, AMS 5]
theorem IsCycleContinuous.comp {U : Type*} [Finite U] [Finite V] [Finite W]
    {G : SimpleGraph U} {H : SimpleGraph V} {K : SimpleGraph W}
    {g : H.edgeSet → K.edgeSet} {f : G.edgeSet → H.edgeSet}
    (hg : IsCycleContinuous g) (hf : IsCycleContinuous f) : IsCycleContinuous (g ∘ f) :=
  fun C hC => hf _ (hg C hC)

end JaegersPetersenColoringConjecture
