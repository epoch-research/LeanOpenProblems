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
# The reconstruction conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Reconstruction_conjecture)
* [Ke57] Kelly, P. J. (1957). "A congruence theorem for trees." *Pacific J. Math.* 7,
  pp. 961--968.
* [Ul60] Ulam, S. M. (1960). *A Collection of Mathematical Problems.* Interscience, New York.
* [Ha64] Harary, F. (1964). "On the reconstruction of a graph from a collection of subgraphs."
  In *Theory of Graphs and its Applications*, Academia, Prague, pp. 47--52.
* [Lo72] Lovász, L. (1972). "A note on the line reconstruction problem." *J. Combin. Theory
  Ser. B* 13, pp. 309--310.
* [Mu77] Müller, V. (1977). "The edge reconstruction hypothesis is true for graphs with more
  than n·log n edges." *J. Combin. Theory Ser. B* 22, pp. 281--283.
* [Bo91] Bondy, J. A. (1991). "A graph reconstructor's manual." In *Surveys in Combinatorics*,
  LMS Lecture Note Series 166, Cambridge University Press, pp. 221--252.
-/

namespace ReconstructionConjecture

variable {V W : Type*}

/-- Two graphs are **hypomorphic** if there is a bijection `σ` between their vertex sets such
that the vertex-deleted subgraphs `G - v` and `H - σ v` are isomorphic for every vertex `v`;
i.e. `G` and `H` have the same deck of vertex-deleted subgraphs. -/
def Hypomorphic (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : V ≃ W, ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)

/-- Two graphs are **edge-hypomorphic** if there is a bijection `σ` between their edge sets
such that the edge-deleted subgraphs `G - e` and `H - σ e` are isomorphic for every edge `e`;
i.e. `G` and `H` have the same deck of edge-deleted subgraphs. -/
def EdgeHypomorphic (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : G.edgeSet ≃ H.edgeSet, ∀ e : G.edgeSet,
    Nonempty (G.deleteEdges {(e : Sym2 V)} ≃g H.deleteEdges {((σ e : H.edgeSet) : Sym2 W)})

/--
**The edge reconstruction conjecture** (Harary [Ha64]).

Every finite simple graph with at least four edges is determined up to isomorphism by its
deck of edge-deleted subgraphs: any two edge-hypomorphic graphs on the same vertex set with
at least four edges are isomorphic.
-/
theorem edge_reconstruction_conjecture {V : Type} [Fintype V] (G H : SimpleGraph V)
    (hE : 4 ≤ G.edgeSet.ncard) (h : EdgeHypomorphic G H) : Nonempty (G ≃g H) := by
  sorry

end ReconstructionConjecture

theorem ReconstructionConjecture.edge_reconstruction_conjecture.disproof : ¬ (type_of% @ReconstructionConjecture.edge_reconstruction_conjecture) := sorry
