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
# Tuza's conjecture

Tuza's conjecture (1981) concerns triangles in finite undirected graphs. For a graph $G$ let
$\nu(G)$ be the *triangle packing number*, the largest number of pairwise edge-disjoint
triangles in $G$, and let $\tau(G)$ be the *triangle hitting number*, the smallest size of a
set of edges meeting every triangle of $G$. Trivially $\nu(G) \le \tau(G) \le 3\nu(G)$.
Tuza conjectured that $\tau(G) \le 2\nu(G)$ for every graph $G$.

*References:*
- [Wikipedia: Tuza's conjecture](https://en.wikipedia.org/wiki/Tuza%27s_conjecture)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- Tuza, Zs. (1981). "Conjecture." In *Finite and Infinite Sets, Proc. Colloq. Math. Soc. János
  Bolyai*, Eger, Hungary, p. 888.
-/

open Finset SimpleGraph

namespace TuzasConjecture

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/--
A finite set `T` of triangles of `G` (a triangle is a `3`-clique, given by its vertex set) is a
*triangle packing* if its triangles are pairwise edge-disjoint, i.e. no edge of `G` lies in two
distinct triangles of `T`.
-/
def IsTrianglePacking (T : Finset (Finset V)) : Prop :=
  T ⊆ G.cliqueFinset 3 ∧
    ∀ s ∈ T, ∀ t ∈ T, s ≠ t → ∀ e ∈ G.edgeFinset, e ∈ s.sym2 → e ∉ t.sym2

/--
The *triangle packing number* $\nu(G)$ of a finite graph $G$: the largest number of pairwise
edge-disjoint triangles in $G$.
-/
noncomputable def trianglePackingNumber : ℕ :=
  sSup {n | ∃ T, IsTrianglePacking G T ∧ T.card = n}

/--
A set `E` of edges of `G` is a *triangle hitting set* if every triangle of `G` contains an edge
of `E`.
-/
def IsTriangleHittingSet (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2

/--
The *triangle hitting number* $\tau(G)$ of a finite graph $G$: the smallest size of a set of edges
of $G$ meeting every triangle of $G$.
-/
noncomputable def triangleHittingNumber : ℕ :=
  sInf {n | ∃ E, IsTriangleHittingSet G E ∧ E.card = n}

/--
**Tuza's conjecture.** Let $G$ be a finite simple undirected graph and let $\nu(G)$ be the
maximum number of pairwise edge-disjoint triangles in $G$. Can all triangles of $G$ be hit by a
set of at most $2\nu(G)$ edges? That is, is there a set of at most $2\nu(G)$ edges of $G$ that
contains an edge of every triangle of $G$?
-/
theorem tuzas_conjecture : 
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      ∃ E, IsTriangleHittingSet G E ∧ E.card ≤ 2 * trianglePackingNumber G := by
  sorry

end TuzasConjecture

theorem TuzasConjecture.tuzas_conjecture.disproof : ¬ (type_of% @TuzasConjecture.tuzas_conjecture) := sorry
