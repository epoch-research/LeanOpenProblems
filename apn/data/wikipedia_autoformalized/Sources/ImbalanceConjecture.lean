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
# Imbalance conjecture

For a finite simple undirected graph $G$, the *imbalance* of an edge $e = uv$ is
$\operatorname{imb}(e) = |\deg(u) - \deg(v)|$. The *imbalance sequence* $M_G$ is the multiset
of the imbalances of all edges of $G$. A multiset of natural numbers is *graphic* if it is the
degree sequence of some finite simple graph.

The imbalance conjecture (Kozerenko–Skochko, 2014) asks whether $M_G$ is graphic whenever every
edge of $G$ has imbalance at least $1$.

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/imbalance_conjecture)
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Graph_theory)
* [KS14] Kozerenko, S. and Skochko, V. (2014). "On graphs with graphic imbalance sequences."
  *Algebra and Discrete Mathematics* 18(1), pp. 97--108.
* [KS23] Kozerenko, S. and Serdiuk, A. (2023). "New results on imbalance graphic graphs."
  *Opuscula Mathematica* 43(1), pp. 81--100.
-/

open SimpleGraph

namespace ImbalanceConjecture

variable {V : Type*} [Fintype V]

/-- The imbalance of an edge $e = uv$ of `G` is $|\deg(u) - \deg(v)|$. -/
def imbalance (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) : ℕ :=
  Sym2.lift ⟨fun u v => ((G.degree u : ℤ) - G.degree v).natAbs,
    fun u v => by dsimp only; omega⟩ e

@[category API, AMS 5]
lemma imbalance_mk (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    imbalance G s(u, v) = ((G.degree u : ℤ) - G.degree v).natAbs :=
  rfl

/-- The imbalance sequence $M_G$ of `G`: the multiset of the imbalances of all edges of `G`,
each (undirected) edge counted once. -/
def imbalanceMultiset [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Multiset ℕ :=
  G.edgeFinset.val.map (imbalance G)

/-- A multiset `M` of natural numbers is *graphic* if it is the degree sequence of some finite
simple graph, i.e. `M` is the multiset of vertex degrees of some `SimpleGraph (Fin n)`. -/
def IsGraphic (M : Multiset ℕ) : Prop :=
  ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (_ : DecidableRel H.Adj), H.degreeMultiset = M

/-- The empty multiset is graphic: it is the degree sequence of the graph with no vertices. -/
@[category test, AMS 5]
lemma isGraphic_zero : IsGraphic 0 :=
  ⟨0, ⊥, inferInstance, rfl⟩

/-- The multiset $\{1, 1\}$ is graphic: it is the degree sequence of $K_2$. -/
@[category test, AMS 5]
lemma isGraphic_pair_one : IsGraphic {1, 1} :=
  ⟨2, ⊤, inferInstance, by decide⟩

/-- The multiset $\{1\}$ is not graphic: a graph on one vertex has no edges. -/
@[category test, AMS 5]
lemma not_isGraphic_singleton_one : ¬ IsGraphic {1} := by
  rintro ⟨n, H, _, h⟩
  have hn : n = 1 := by
    simpa [degreeMultiset] using congrArg Multiset.card h
  subst hn
  simpa [degreeMultiset] using congrArg Multiset.sum h

/-- The path $P_3$ on three vertices (the complete graph $K_3$ with one edge removed) has
imbalance sequence $\{1, 1\}$. -/
@[category test, AMS 5]
lemma imbalanceMultiset_pathThree :
    imbalanceMultiset ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(1, 2)}) = {1, 1} := by
  decide

/-- Every edge of the path $P_3$ has imbalance at least $1$, so $P_3$ satisfies the hypothesis of
the imbalance conjecture. -/
@[category test, AMS 5]
lemma one_le_imbalance_pathThree :
    ∀ e ∈ ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(1, 2)}).edgeSet,
      1 ≤ imbalance ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(1, 2)}) e := by
  decide

/-- The complete graph $K_3$ has three edges, each of imbalance $0$. -/
@[category test, AMS 5]
lemma imbalanceMultiset_completeGraph_three :
    imbalanceMultiset (⊤ : SimpleGraph (Fin 3)) = {0, 0, 0} := by
  decide

/-- The edgeless graph has empty imbalance sequence. -/
@[category test, AMS 5]
lemma imbalanceMultiset_bot [DecidableEq V] : imbalanceMultiset (⊥ : SimpleGraph V) = 0 := by
  simp [imbalanceMultiset]

/--
**The imbalance conjecture** (Kozerenko–Skochko, 2014).

Let $G$ be a finite simple undirected graph. If the imbalance
$\operatorname{imb}(e) = |\deg(u) - \deg(v)|$ of every edge $e = uv$ of $G$ is at least $1$
(equivalently, no edge joins two vertices of equal degree), is the multiset $M_G$ of all edge
imbalances always graphic, i.e. the degree sequence of some finite simple graph?
-/
@[category research open, AMS 5]
theorem imbalance_conjecture : answer(sorry) ↔
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ e ∈ G.edgeSet, 1 ≤ imbalance G e) → IsGraphic (imbalanceMultiset G) := by
  sorry

end ImbalanceConjecture
