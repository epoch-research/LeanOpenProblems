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
# Apex graphs and Jørgensen's conjecture

*References:*
- [Wikipedia, Apex graph](https://en.wikipedia.org/wiki/apex_graph)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Jø94] Jørgensen, L. K., *Contractions to $K_8$*. J. Graph Theory 18 (1994), 431–448.
- [KNTW12] Kawarabayashi, K., Norine, S., Thomas, R., Wollan, P.,
  *$K_6$ minors in large 6-connected graphs*. [arXiv:1203.2192](https://arxiv.org/abs/1203.2192)

An *apex graph* is a graph that can be made planar by the removal of a single vertex.
Jørgensen conjectured that every $6$-connected graph with no $K_6$ minor is an apex graph.
Kawarabayashi, Norine, Thomas and Wollan proved the conjecture for all sufficiently large
graphs, so a false conjecture would have only finitely many counterexamples.

Mathlib has neither planarity nor graph minors, so this file defines both. Planarity is defined
by a drawing in the plane without crossings, and a minor is defined by branch sets.
-/

namespace ApexGraph

open SimpleGraph unitInterval
open scoped EuclideanGeometry

variable {V W : Type*}

/-- A graph `G` is *planar* if it has a drawing in the plane $\mathbb{R}^2$: the vertices are
sent to distinct points and each edge is sent to an arc (an injective continuous image of the unit
interval) joining the images of its two ends. The interior of an arc contains no vertex, and the
interior of an arc meets no other arc. Two distinct arcs thus meet only in common endpoints.

By Wagner's theorem a finite graph is planar in this sense exactly when it has neither $K_5$
nor $K_{3,3}$ as a minor. -/
def IsPlanar (G : SimpleGraph V) : Prop :=
  ∃ (f : V → ℝ²) (γ : G.edgeSet → I → ℝ²),
    Function.Injective f ∧
    (∀ e, Continuous (γ e) ∧ Function.Injective (γ e)) ∧
    (∀ e : G.edgeSet, s(γ e 0, γ e 1) = (e : Sym2 V).map f) ∧
    (∀ e, ∀ t, t ≠ 0 → t ≠ 1 → γ e t ∉ Set.range f) ∧
    (∀ e e', e ≠ e' → ∀ t t', t ≠ 0 → t ≠ 1 → γ e t ≠ γ e' t')

/-- A graph `G` is an *apex graph* if it has a vertex `v` whose deletion leaves a planar graph.
Such a vertex is called an *apex* of `G`.

Wikipedia also counts the null graph (no vertices) as an apex graph. This definition does not,
but the two agree on every graph with a vertex, and in particular on every $6$-connected graph. -/
def IsApex (G : SimpleGraph V) : Prop :=
  ∃ v : V, IsPlanar (G.induce {v}ᶜ)

/-- The graph `H` is a *minor* of the graph `G` if `H` can be obtained from a subgraph of `G` by
contracting edges. Equivalently, and this is the form used here, there are *branch sets*
`B w ⊆ V(G)` for `w ∈ V(H)` which are pairwise disjoint and each induce a connected (hence
nonempty) subgraph of `G`, such that for every edge `w w'` of `H` some edge of `G` joins `B w`
to `B w'`. -/
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ B : W → Set V, (∀ w, (G.induce (B w)).Connected) ∧
    Pairwise (fun w w' ↦ Disjoint (B w) (B w')) ∧
    ∀ w w', H.Adj w w' → ∃ u ∈ B w, ∃ v ∈ B w', G.Adj u v

/-- **Jørgensen's conjecture** [Jø94]. Every $6$-connected graph with no $K_6$ minor is an apex
graph. That is, if a finite graph $G$ has more than $6$ vertices, stays connected after the
deletion of any set of fewer than $6$ vertices, and does not contain the complete graph $K_6$ as
a minor, then $G$ has a vertex whose deletion leaves a planar graph.

Kawarabayashi, Norine, Thomas and Wollan [KNTW12] proved the conjecture for all sufficiently
large graphs, so a false conjecture would have only finitely many counterexamples. -/
theorem apex_graph [Fintype V] (G : SimpleGraph V) (h₆ : IsKConnected G 6)
    (hK₆ : ¬ IsMinor (completeGraph (Fin 6)) G) : IsApex G := by
  sorry

end ApexGraph

theorem ApexGraph.apex_graph.disproof : ¬ (type_of% @ApexGraph.apex_graph) := sorry
