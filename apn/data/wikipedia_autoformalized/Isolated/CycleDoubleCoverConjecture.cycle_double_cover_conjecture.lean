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
# Cycle double cover conjecture

*References:*
- [Wikipedia, Cycle double cover](https://en.wikipedia.org/wiki/cycle_double_cover_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Sz73] Szekeres, G., *Polyhedral decompositions of cubic graphs*,
  Bull. Austral. Math. Soc. 8 (1973), 367--387.
- [Se79] Seymour, P. D., *Sums of circuits*, in Graph Theory and Related Topics (1979), 341--355.

A *cycle double cover* of a graph is a collection of cycles that together include each edge of
the graph exactly twice. The **cycle double cover conjecture** states that every bridgeless graph
has a cycle double cover.

Here a *cycle* is a connected subgraph all of whose vertices have degree two, so a single edge
traversed back and forth is not a cycle. Cycle graphs and bridgeless cactus graphs only have
double covers that use the same cycle twice, so the collection is a *multiset* of cycles and
edges are counted with multiplicity.

The conjecture is stated for finite simple graphs. This loses no generality: subdividing every
edge of a bridgeless multigraph gives a bridgeless simple graph, and a cycle double cover of the
subdivision contracts to one of the original multigraph.
-/

open SimpleGraph

namespace CycleDoubleCoverConjecture

variable {V : Type*} [DecidableEq V]

/-- A multiset `C` of cycles of `G` is a *cycle double cover* of `G` if every edge of `G` lies in
exactly two members of `C`, counted with multiplicity. -/
def IsCycleDoubleCover (G : SimpleGraph V) (C : Multiset (Cycle G)) : Prop :=
  ∀ e ∈ G.edgeSet, C.countP (fun c => e ∈ c.edges) = 2

/--
**Cycle double cover conjecture** (Szekeres 1973, Seymour 1979).
Every bridgeless graph has a family of cycles that includes each edge twice.
Precisely: for every finite bridgeless undirected graph $G$ there is a multiset of cycles
of $G$ such that every edge of $G$ belongs to exactly two members of the multiset, counted with
multiplicity.
-/
theorem cycle_double_cover_conjecture [Fintype V] (G : SimpleGraph V) (hG : G.IsBridgeless) :
    ∃ C : Multiset (Cycle G), IsCycleDoubleCover G C := by
  sorry

/-- The triangle `0 → 1 → 2 → 0` as a cycle of the complete graph on three vertices. -/
def triangleCycle : Cycle (⊤ : SimpleGraph (Fin 3)) where
  base := 0
  walk := .cons (u := 0) (v := 1) (by decide) (.cons (u := 1) (v := 2) (by decide)
    (.cons (u := 2) (v := 0) (by decide) .nil))
  isCycle := by
    rw [Walk.isCycle_def, Walk.isTrail_def]
    exact ⟨by decide, by simp, by decide⟩

end CycleDoubleCoverConjecture

theorem CycleDoubleCoverConjecture.cycle_double_cover_conjecture.disproof : ¬ (type_of% @CycleDoubleCoverConjecture.cycle_double_cover_conjecture) := sorry
