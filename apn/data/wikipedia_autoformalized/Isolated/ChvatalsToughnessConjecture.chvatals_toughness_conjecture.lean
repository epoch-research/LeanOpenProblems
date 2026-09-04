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
# Chvátal's toughness conjecture

A finite simple graph $G$ is *$t$-tough* (Chvátal, 1973), for a real number $t$, if for every
set $S$ of vertices such that $G - S$ has more than one connected component,
$|S| \ge t \cdot \omega(G - S)$, where $\omega(G - S)$ is the number of connected components of
$G - S$. Equivalently, for every integer $k > 1$, $G$ cannot be split into $k$ connected
components by removing fewer than $tk$ vertices. Complete graphs cannot be disconnected by
removing vertices, so they are $t$-tough for every $t$ (by convention they have infinite
toughness).

Chvátal observed that every Hamiltonian graph is $1$-tough and conjectured that, conversely,
there is a threshold $t$ such that every $t$-tough graph is Hamiltonian. His original guess
$t = 2$ was disproved by Bauer, Broersma and Veldman (2000), but the existence of some threshold
remains open and is known as Chvátal's toughness conjecture.

*References:*
- [Wikipedia, Graph toughness](https://en.wikipedia.org/wiki/Graph_toughness)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [V. Chvátal, *Tough graphs and Hamiltonian circuits*,
  Discrete Math. 5 (1973)](https://doi.org/10.1016/0012-365X(73)90138-6)
- [D. Bauer, H. J. Broersma, H. J. Veldman, *Not every 2-tough graph is Hamiltonian*,
  Discrete Appl. Math. 99 (2000)](https://doi.org/10.1016/S0166-218X(99)00141-9)
- [D. Bauer, H. Broersma, E. Schmeichel, *Toughness in graphs — a survey*,
  Graphs Combin. 22 (2006)](https://doi.org/10.1007/s00373-006-0649-0)
-/

namespace ChvatalsToughnessConjecture

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {s t : ℝ}

/-- A finite simple graph `G` is `t`-tough (for a real number `t`) if for every set `S` of
vertices such that `G - S` has more than one connected component, `t * ω(G - S) ≤ |S|`, where
`ω(G - S)` is the number of connected components of the graph `G - S` obtained from `G` by
deleting the vertices in `S`. Here `G - S` is the subgraph of `G` induced on the complement
of `S`.

Complete graphs are `t`-tough for every `t`, because no set of vertices disconnects them. -/
def IsTough [Finite V] (G : SimpleGraph V) (t : ℝ) : Prop :=
  ∀ S : Set V, 1 < Nat.card (G.induce Sᶜ).ConnectedComponent →
    t * Nat.card (G.induce Sᶜ).ConnectedComponent ≤ S.ncard

/--
**Chvátal's toughness conjecture** (Chvátal, 1973): there is a number $t$ such that every
$t$-tough finite simple graph on at least three vertices is Hamiltonian.

The restriction to at least three vertices excludes the empty graph and the complete graph on
two vertices, which are `t`-tough for every `t` but have no Hamiltonian cycle.
-/
theorem chvatals_toughness_conjecture :
    ∃ t : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      3 ≤ Fintype.card V → IsTough G t → G.IsHamiltonian := by
  sorry

end ChvatalsToughnessConjecture

theorem ChvatalsToughnessConjecture.chvatals_toughness_conjecture.disproof : ¬ (type_of% @ChvatalsToughnessConjecture.chvatals_toughness_conjecture) := sorry
