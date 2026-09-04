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

/-- The imbalance sequence $M_G$ of `G`: the multiset of the imbalances of all edges of `G`,
each (undirected) edge counted once. -/
def imbalanceMultiset [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Multiset ℕ :=
  G.edgeFinset.val.map (imbalance G)

/-- A multiset `M` of natural numbers is *graphic* if it is the degree sequence of some finite
simple graph, i.e. `M` is the multiset of vertex degrees of some `SimpleGraph (Fin n)`. -/
def IsGraphic (M : Multiset ℕ) : Prop :=
  ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (_ : DecidableRel H.Adj), H.degreeMultiset = M

/--
**The imbalance conjecture** (Kozerenko–Skochko, 2014).

Let $G$ be a finite simple undirected graph. If the imbalance
$\operatorname{imb}(e) = |\deg(u) - \deg(v)|$ of every edge $e = uv$ of $G$ is at least $1$
(equivalently, no edge joins two vertices of equal degree), is the multiset $M_G$ of all edge
imbalances always graphic, i.e. the degree sequence of some finite simple graph?
-/
theorem imbalance_conjecture : 
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ e ∈ G.edgeSet, 1 ≤ imbalance G e) → IsGraphic (imbalanceMultiset G) := by
  sorry

end ImbalanceConjecture

theorem ImbalanceConjecture.imbalance_conjecture.disproof : ¬ (type_of% @ImbalanceConjecture.imbalance_conjecture) := sorry
