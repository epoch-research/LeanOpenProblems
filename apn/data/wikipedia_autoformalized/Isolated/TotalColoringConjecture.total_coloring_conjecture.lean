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
# Total coloring conjecture

A *total coloring* of a graph $G$ assigns a color to every vertex and every edge of $G$ so that
adjacent vertices, adjacent edges, and an edge and either of its endpoints never receive the same
color. The *total chromatic number* $\chi''(G)$ is the least number of colors in a total coloring
of $G$; equivalently, it is the chromatic number of the *total graph* $T(G)$, whose vertices are
the vertices and edges of $G$, two of them being adjacent when the corresponding elements of $G$
are adjacent or incident.

The total coloring conjecture of Behzad and Vizing states that every finite simple graph $G$
satisfies $\chi''(G) \leq \Delta(G) + 2$, where $\Delta(G)$ is the maximum degree of $G$.

*References:*
- [Wikipedia, Total coloring](https://en.wikipedia.org/wiki/total_coloring_conjecture)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
-/

namespace TotalColoringConjecture

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/--
The total graph $T(G)$ of a simple graph `G`. Its vertices are the vertices of `G` (`Sum.inl v`)
together with the edges of `G` (`Sum.inr e`). Two vertices of `G` are adjacent in $T(G)$ if they are
adjacent in `G`; two edges of `G` are adjacent in $T(G)$ if they are distinct and share an endpoint
(that is, they are adjacent in the line graph of `G`); a vertex and an edge of `G` are adjacent in
$T(G)$ if the vertex is an endpoint of the edge.
-/
def totalGraph : SimpleGraph (V ⊕ G.edgeSet) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inl v, .inr e => v ∈ (e : Sym2 V)
    | .inr e, .inl v => v ∈ (e : Sym2 V)
    | .inr e, .inr f => G.lineGraph.Adj e f
  symm := by
    rintro (u | e) (v | f) h
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    rintro (v | e) h
    · exact G.loopless v h
    · exact G.lineGraph.loopless e h

/--
The total chromatic number $\chi''(G)$ of a simple graph `G`: the least number of colors in a
(proper) total coloring of `G`, that is, the chromatic number of the total graph of `G`.
-/
noncomputable def totalChromaticNumber : ℕ∞ := (totalGraph G).chromaticNumber

/-- The vertices of `G` induce a copy of `G` inside its total graph. -/
def totalGraphEmbeddingInl : G ↪g totalGraph G where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Iff.rfl

/-- The edges of `G` induce a copy of the line graph of `G` inside the total graph of `G`. -/
def totalGraphEmbeddingInr : G.lineGraph ↪g totalGraph G where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := Iff.rfl

/--
**Total coloring conjecture** (Behzad, Vizing). For every finite simple graph $G$ the total
chromatic number is at most two plus the maximum degree: $\chi''(G) \leq \Delta(G) + 2$.
-/
theorem total_coloring_conjecture [Fintype V] [DecidableRel G.Adj] :
    totalChromaticNumber G ≤ G.maxDegree + 2 := by
  sorry

end TotalColoringConjecture

theorem TotalColoringConjecture.total_coloring_conjecture.disproof : ¬ (type_of% @TotalColoringConjecture.total_coloring_conjecture) := sorry
