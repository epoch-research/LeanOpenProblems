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
theorem jaegers_petersen_coloring_conjecture [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : G.IsRegularOfDegree 3) (hbridgeless : G.IsBridgeless) :
    ∃ f : G.edgeSet → petersenGraph.edgeSet, IsCycleContinuous f := by
  sorry

end JaegersPetersenColoringConjecture

theorem JaegersPetersenColoringConjecture.jaegers_petersen_coloring_conjecture.disproof : ¬ (type_of% @JaegersPetersenColoringConjecture.jaegers_petersen_coloring_conjecture) := sorry
