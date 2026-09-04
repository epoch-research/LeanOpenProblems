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
# List coloring conjecture

An instance of a list edge-coloring problem consists of a graph $G$ together with a list of
allowed colors for each edge. A list edge-coloring is a choice of a color for each edge from its
list; it is proper if no two adjacent edges (edges sharing a vertex) receive the same color.
The graph $G$ is $k$-edge-choosable if every such instance with at least $k$ allowed colors on
every edge has a proper list edge-coloring. The list chromatic index $\operatorname{ch}'(G)$ is
the least $k$ such that $G$ is $k$-edge-choosable, and the chromatic index $\chi'(G)$ is the
least number of colors in a proper edge-coloring of $G$.

The list coloring conjecture states that $\operatorname{ch}'(G) = \chi'(G)$ for every graph $G$.

*References:*
- [Wikipedia, List edge-coloring](https://en.wikipedia.org/wiki/list_coloring_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [JT95] Jensen, T. R. and Toft, B., *Graph Coloring Problems*. Wiley-Interscience (1995).
- [Ga95] Galvin, F., *The list chromatic index of a bipartite multigraph*. J. Combin. Theory
  Ser. B 63 (1995), 153–158.
- [Ka00] Kahn, J., *Asymptotics of the list chromatic index for multigraphs*. Random Structures
  & Algorithms 17 (2000), 117–156.
-/

namespace ListColoringConjecture

open SimpleGraph

variable {V : Type*}

/--
A graph `G` is `k`-edge-choosable if for every assignment `L` of a finite list of colors to each
edge of `G` with at least `k` colors on every edge, there is a proper edge-coloring of `G` that
colors each edge `e` with a color from `L e`.

A proper edge-coloring of `G` is a proper vertex coloring of the line graph `G.lineGraph`, whose
vertices are the edges of `G`, two of them being adjacent when they share a vertex of `G`.
Colors are taken from `ℕ`; for a finite graph this loses no generality, as only finitely many
colors appear in the lists.
-/
def IsEdgeChoosable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : G.edgeSet → Finset ℕ, (∀ e, k ≤ (L e).card) →
    ∃ C : G.lineGraph.Coloring ℕ, ∀ e, C e ∈ L e

/--
The list chromatic index (edge choosability) $\operatorname{ch}'(G)$ of a graph `G` is the least
`k` such that `G` is `k`-edge-choosable, or `⊤` if there is no such `k`.
-/
noncomputable def listChromaticIndex (G : SimpleGraph V) : ℕ∞ :=
  ⨅ k ∈ setOf (IsEdgeChoosable G), (k : ℕ∞)

/--
The chromatic index $\chi'(G)$ of a graph `G` is the least number of colors in a proper
edge-coloring of `G`, that is, the chromatic number of the line graph of `G`.
-/
noncomputable def chromaticIndex (G : SimpleGraph V) : ℕ∞ :=
  G.lineGraph.chromaticNumber

/--
**The list coloring conjecture.** For every finite (simple) graph $G$, the list chromatic index
equals the chromatic index:
$$\operatorname{ch}'(G) = \chi'(G).$$

Since $\chi'(G) \le \operatorname{ch}'(G)$ always holds, the content of the conjecture is the
inequality $\operatorname{ch}'(G) \le \chi'(G)$. The conjecture has a fuzzy origin; Jensen and
Toft [JT95] overview its history. The Dinitz conjecture, proven by Galvin [Ga95], is the special
case of the complete bipartite graphs $K_{n,n}$. Kahn [Ka00] proved that
$\operatorname{ch}'(G) \le (1 + o(1)) \chi'(G)$, so the two indices agree asymptotically.
-/
theorem list_coloring_conjecture [Fintype V] (G : SimpleGraph V) :
    listChromaticIndex G = chromaticIndex G := by
  sorry

end ListColoringConjecture

theorem ListColoringConjecture.list_coloring_conjecture.disproof : ¬ (type_of% @ListColoringConjecture.list_coloring_conjecture) := sorry
