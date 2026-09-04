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
# Second neighborhood problem

Seymour's second neighborhood conjecture (1990) asks whether every oriented graph contains a
vertex for which there are at least as many other vertices at (directed) distance two as at
distance one.

An *oriented graph* is a finite directed graph obtained from a simple undirected graph by
assigning an orientation to each edge. Equivalently, it is a directed graph with no loops, no
parallel arcs and no two-edge cycles (digons). A Mathlib `Digraph V` is a relation on `V`, so it
has no parallel arcs by construction; we only need to require the absence of loops and digons.

The *first neighborhood* $N^+(v)$ of a vertex $v$ is the set of vertices at out-distance one
from $v$ (its out-neighbors) and the *second neighborhood* $N^{++}(v)$ is the set of vertices
at out-distance exactly two from $v$, i.e.
$N^{++}(v) = \{w \notin \{v\} \cup N^+(v) : N^-(w) \cap N^+(v) \neq \emptyset\}$.
These sets are disjoint and neither contains $v$.
A vertex $v$ with $|N^{++}(v)| \geq |N^+(v)|$ is called a *Seymour vertex*.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/second_neighborhood_problem)
- [Wikipedia: List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [DeLa95] Dean, N. and Latka, B. J. (1995). "Squaring the tournament—an open problem."
  *Congressus Numerantium* 109, pp. 73--80.
- [arXiv:1808.02247](https://arxiv.org/abs/1808.02247) Dara, S., Francis, M. C., Jacob, D.,
  Narayanan, N. (2018). "Extending some results on the second neighborhood conjecture."
-/

namespace SecondNeighborhoodProblem

variable {V : Type*} (D : Digraph V)

/--
A digraph `D` is an *oriented graph* if it has no loops and no digons (two-edge cycles), i.e.
if there is an arc from `u` to `v`, then there is no arc from `v` to `u`. Since a `Digraph` is a
relation on its vertex type, it has no parallel arcs by construction.
-/
def IsOriented : Prop :=
  (∀ v, ¬ D.Adj v v) ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u)

/--
The (first) out-neighborhood $N^+(v)$ of a vertex `v` in a digraph `D`: the set of vertices at
out-distance one from `v`, i.e. the heads of the arcs leaving `v`.
-/
def outNeighborSet (v : V) : Set V :=
  {w | D.Adj v w}

/--
The second out-neighborhood $N^{++}(v)$ of a vertex `v` in a digraph `D`: the set of vertices at
out-distance exactly two from `v`. These are the vertices `w` distinct from `v` and not in
$N^+(v)$ that are out-neighbors of some out-neighbor of `v`.
-/
def secondOutNeighborSet (v : V) : Set V :=
  {w | w ≠ v ∧ ¬ D.Adj v w ∧ ∃ u, D.Adj v u ∧ D.Adj u w}

/--
A vertex `v` of a (finite) digraph `D` is a *Seymour vertex* if its second out-neighborhood is
at least as large as its first out-neighborhood, i.e. $|N^{++}(v)| \geq |N^+(v)|$.
-/
def IsSeymourVertex (v : V) : Prop :=
  (outNeighborSet D v).ncard ≤ (secondOutNeighborSet D v).ncard

/-- A digraph is an oriented graph if and only if it is an orientation of some simple graph. -/
@[category API, AMS 5]
theorem isOriented_iff_exists_isOrientation :
    IsOriented D ↔ ∃ H : SimpleGraph V, D.IsOrientation H := by
  constructor
  · rintro ⟨hloop, hasymm⟩
    refine ⟨D.toSimpleGraphInclusive, fun u v huv => ⟨?_, Or.inl huv⟩,
      fun u v huv => ⟨hasymm u v, fun hvu => huv.2.resolve_right hvu⟩⟩
    rintro rfl
    exact hloop u huv
  · rintro ⟨H, hDH, hH⟩
    refine ⟨fun v hv => (hDH v v hv).ne rfl, fun u v huv => ?_⟩
    exact (hH u v (hDH u v huv)).mp huv

/-- The first and second out-neighborhoods of a vertex are disjoint. -/
@[category API, AMS 5]
theorem disjoint_outNeighborSet_secondOutNeighborSet (v : V) :
    Disjoint (outNeighborSet D v) (secondOutNeighborSet D v) :=
  Set.disjoint_left.mpr fun _ hw hw' => hw'.2.1 hw

/-- In an oriented graph, a vertex is not in its own out-neighborhood. -/
@[category API, AMS 5]
theorem notMem_outNeighborSet_self (hD : IsOriented D) (v : V) : v ∉ outNeighborSet D v :=
  hD.1 v

/-- A vertex is not in its own second out-neighborhood. -/
@[category API, AMS 5]
theorem notMem_secondOutNeighborSet_self (v : V) : v ∉ secondOutNeighborSet D v :=
  fun h => h.1 rfl

/--
**The second neighborhood problem** (Seymour's second neighborhood conjecture, 1990).

Does every oriented graph contain a vertex for which there are at least as many other vertices
at distance two as at distance one? That is, does every finite oriented graph $D$ have a vertex
$v$ with $|N^{++}(v)| \geq |N^{+}(v)|$, where $N^{+}(v)$ is the set of vertices at out-distance
one from $v$ and $N^{++}(v)$ is the set of vertices at out-distance exactly two from $v$?

The vertex set is required to be nonempty, since the empty digraph has no vertex at all.
-/
@[category research open, AMS 5]
theorem second_neighborhood_problem :
    answer(sorry) ↔
      ∀ (V : Type*) [Fintype V] [Nonempty V] (D : Digraph V), IsOriented D →
        ∃ v, IsSeymourVertex D v := by
  sorry

/-- A sink (a vertex of out-degree zero) is a Seymour vertex. -/
@[category test, AMS 5]
theorem isSeymourVertex_of_forall_not_adj (v : V) (h : ∀ w, ¬ D.Adj v w) :
    IsSeymourVertex D v := by
  simp [IsSeymourVertex, outNeighborSet, h]

/-- The directed triangle `0 → 1 → 2 → 0` on three vertices. -/
def directedTriangle : Digraph (ZMod 3) where
  Adj u v := v = u + 1

/-- The directed triangle is an oriented graph. -/
@[category test, AMS 5]
theorem isOriented_directedTriangle : IsOriented directedTriangle := by
  unfold IsOriented directedTriangle
  decide

/-- Every vertex of the directed triangle is a Seymour vertex. -/
@[category test, AMS 5]
theorem isSeymourVertex_directedTriangle (v : ZMod 3) : IsSeymourVertex directedTriangle v := by
  have h1 : outNeighborSet directedTriangle v = {v + 1} := by
    ext w
    simp [outNeighborSet, directedTriangle]
  have h2 : secondOutNeighborSet directedTriangle v = {v + 2} := by
    ext w
    simp only [secondOutNeighborSet, directedTriangle, Set.mem_setOf_eq, Set.mem_singleton_iff]
    clear h1
    revert v w
    decide
  unfold IsSeymourVertex
  rw [h1, h2]
  simp

/--
The digon `0 → 1 → 0` on two vertices. It is not an oriented graph, and the condition excluding
digons is necessary: the digon has no Seymour vertex.
-/
def digon : Digraph (Fin 2) where
  Adj u v := u ≠ v

/-- The digon is not an oriented graph. -/
@[category test, AMS 5]
theorem not_isOriented_digon : ¬ IsOriented digon :=
  fun h => h.2 0 1 (by simp [digon]) (by simp [digon])

/-- The digon has no Seymour vertex. -/
@[category test, AMS 5]
theorem not_isSeymourVertex_digon (v : Fin 2) : ¬ IsSeymourVertex digon v := by
  have h1 : outNeighborSet digon v = {v + 1} := by
    ext w
    simp only [outNeighborSet, digon, Set.mem_setOf_eq, Set.mem_singleton_iff]
    revert v w
    decide
  have h2 : secondOutNeighborSet digon v = ∅ := by
    ext w
    simp only [secondOutNeighborSet, digon, Set.mem_setOf_eq, Set.mem_empty_iff_false]
    clear h1
    revert v w
    decide
  unfold IsSeymourVertex
  rw [h1, h2]
  simp

end SecondNeighborhoodProblem
