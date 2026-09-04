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
# Reconstruction conjecture

The *deck* of a finite graph $G$ is the multiset of isomorphism classes of the vertex-deleted
subgraphs $G - v$, one *card* for each vertex $v$ of $G$. The reconstruction conjecture of Kelly
and Ulam says that a graph on at least three vertices is determined, up to isomorphism, by its
deck.

The analogous statement for digraphs is false (Stockmeyer). The new digraph reconstruction
conjecture of Ramachandran instead attaches to each card $D - v$ the degree pair
$(\deg^{+}(v), \deg^{-}(v))$ of the deleted vertex, and says that every finite digraph is
determined, up to isomorphism, by this degree-associated deck.

*References:*
- [Wikipedia, *Reconstruction conjecture*](https://en.wikipedia.org/wiki/reconstruction_conjecture)
- [Wikipedia, *New digraph reconstruction conjecture*](https://en.wikipedia.org/wiki/New_digraph_reconstruction_conjecture)
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- P. J. Kelly, *A congruence theorem for trees*, Pacific J. Math. 7 (1957), 961–968.
- S. Ramachandran, *On a new digraph reconstruction conjecture*, J. Combin. Theory Ser. B
  31 (1981), 143–149.
- P. K. Stockmeyer, *The falsity of the reconstruction conjecture for tournaments*,
  J. Graph Theory 1 (1977), 19–25.
- B. D. McKay, *Reconstruction of small graphs and digraphs*, Australas. J. Combin. 83 (2022),
  [arXiv:2102.01942](https://arxiv.org/abs/2102.01942).
-/

namespace ReconstructionConjecture

variable {V W : Type*}

/- ## Graphs

A *card* of a graph `G` is a vertex-deleted subgraph `G.induce {v}ᶜ`. Two finite graphs have the
same deck (the same multiset of isomorphism classes of cards) exactly when there is a bijection
`σ` between their vertex sets with `G - v ≅ H - σ v` for every vertex `v`. This is the classical
definition of hypomorphic graphs, and we take it as the definition. -/

/--
Two simple graphs `G` and `H` are **hypomorphic** if there is a bijection `σ` between their
vertex sets such that the vertex-deleted subgraphs `G - v` and `H - σ v` are isomorphic for
every vertex `v` of `G`. For finite graphs this says exactly that `G` and `H` have the same deck,
i.e. the same multiset of isomorphism classes of vertex-deleted subgraphs.
-/
def Hypomorphic (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : V ≃ W, ∀ v, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)

/--
**The reconstruction conjecture** (Kelly–Ulam):
any two hypomorphic finite simple graphs on at least three vertices are isomorphic.

That is, a finite simple graph on at least three vertices is determined up to isomorphism by its
deck, the multiset of isomorphism classes of its vertex-deleted subgraphs. The hypothesis of at
least three vertices is needed because the two graphs on two vertices have the same deck. It is
only imposed on `G`, since hypomorphic graphs have the same number of vertices
(`Hypomorphic.card_eq`).
-/
theorem reconstruction_conjecture.parts.i [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hV : 3 ≤ Fintype.card V)
    (hGH : Hypomorphic G H) : Nonempty (G ≃g H) := by
  sorry

/- ## Digraphs

We use Mathlib's `Digraph`, whose adjacency relation is an arbitrary relation `Adj`. In the
digraph reconstruction problem, digraphs are loopless and have at most one arc for each ordered
pair of vertices (so arcs in both directions between two vertices are allowed); we impose
looplessness as a hypothesis. The vertex-deleted subdigraph `D - v` is the restriction
`Subrel D.Adj (· ≠ v)` of `Adj` to the vertices other than `v`, and a digraph isomorphism is a
relation isomorphism `≃r` between adjacency relations. -/

/-- The out-degree of the vertex `v` in the digraph `D`: the number of arcs leaving `v`. -/
noncomputable def outDegree (D : Digraph V) (v : V) : ℕ :=
  {w | D.Adj v w}.ncard

/-- The in-degree of the vertex `v` in the digraph `D`: the number of arcs entering `v`. -/
noncomputable def inDegree (D : Digraph V) (v : V) : ℕ :=
  {w | D.Adj w v}.ncard

/--
Two digraphs `D` and `E` have the same **degree-associated deck** if there is a bijection `σ`
between their vertex sets such that, for every vertex `v` of `D`, the vertex-deleted subdigraphs
`D - v` and `E - σ v` are isomorphic and `v` and `σ v` have the same out-degree and the same
in-degree. For finite digraphs this says exactly that the multisets of degree-associated cards
`(D - v, (deg⁺ v, deg⁻ v))`, with `D - v` taken up to isomorphism, coincide.
-/
def DegreeHypomorphic (D : Digraph V) (E : Digraph W) : Prop :=
  ∃ σ : V ≃ W, ∀ v,
    Nonempty (Subrel D.Adj (· ≠ v) ≃r Subrel E.Adj (· ≠ σ v)) ∧
    outDegree D v = outDegree E (σ v) ∧ inDegree D v = inDegree E (σ v)

end ReconstructionConjecture

theorem ReconstructionConjecture.reconstruction_conjecture.parts.i.disproof : ¬ (type_of% @ReconstructionConjecture.reconstruction_conjecture.parts.i) := sorry
