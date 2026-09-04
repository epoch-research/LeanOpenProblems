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
# Delta-conjecture (1978)

Gurvich's $\Delta$-conjecture on $d$-graphs. A *$d$-graph* $(V; E_1, \dots, E_d)$ is a complete
graph on a finite vertex set $V$ whose edges are coloured by $d$ colours; the *chromatic
component* of colour $i$ is the graph $(V, E_i)$. A triangle $\Delta$ is a triangle whose three
edges have three pairwise distinct colours. The conjecture states that if a $d$-graph contains a
$\Delta$, then one can choose an (inclusion-)maximal independent vertex set $S_i$ in each
chromatic component $(V, E_i)$, $i = 1, \dots, d$, such that $S_1 \cap \dots \cap S_d = \emptyset$.

*References:*
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia: Complete graph](https://en.wikipedia.org/wiki/complete_graph)
- [Gu09] V. Gurvich, *Decomposing complete edge-chromatic graphs and hypergraphs. Revisited*,
  Discrete Applied Mathematics 157 (2009), 3069–3085.
-/

namespace DeltaConjecture1978

open SimpleGraph

/--
**Delta-conjecture (1978).**
Consider a complete graph $(V; E_1, \dots, E_d)$ on a finite vertex set $V$, each edge of which is
coloured by one of $d$ colours, such that there exists a triangle $\Delta$ coloured in three
pairwise distinct colours. Then, in each chromatic component $(V, E_i)$, $i = 1, \dots, d$, one can
choose a maximal independent vertex set $S_i$ such that $S_1 \cap \dots \cap S_d = \emptyset$.

Here the colouring is `C : TopEdgeLabeling V (Fin d)`, i.e. a map from the edges of the complete
graph on `V` to the `d` colours; the chromatic component $(V, E_i)$ is `C.labelGraph i`, and
"maximal" means maximal with respect to inclusion, not of maximum cardinality. The hypothesis
forces $d \ge 3$; a colour that is not used has `Set.univ` as its only maximal independent set.
-/
@[category research open, AMS 5]
theorem delta_conjecture_1978 {V : Type*} [Fintype V] {d : ℕ} (C : TopEdgeLabeling V (Fin d))
    (hΔ : ∃ x y z : V, ∃ i j k : Fin d, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      (C.labelGraph i).Adj x y ∧ (C.labelGraph j).Adj y z ∧ (C.labelGraph k).Adj x z) :
    ∃ S : Fin d → Set V,
      (∀ i, Maximal (C.labelGraph i).IsIndepSet (S i)) ∧ ⋂ i, S i = ∅ := by
  sorry

/-- The hypothesis of the Δ-conjecture is satisfiable: the complete graph on three vertices with
its three edges coloured by three distinct colours contains a Δ. -/
@[category test, AMS 5]
theorem exists_delta :
    ∃ C : TopEdgeLabeling (Fin 3) (Fin 3), ∃ x y z : Fin 3, ∃ i j k : Fin 3,
      i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      (C.labelGraph i).Adj x y ∧ (C.labelGraph j).Adj y z ∧ (C.labelGraph k).Adj x z := by
  refine ⟨fun e => if e.1 = s(0, 1) then 0 else if e.1 = s(1, 2) then 1 else 2,
    0, 1, 2, 0, 1, 2, by decide, by decide, by decide, ?_, ?_, ?_⟩ <;>
  simp [EdgeLabeling.get]

end DeltaConjecture1978
