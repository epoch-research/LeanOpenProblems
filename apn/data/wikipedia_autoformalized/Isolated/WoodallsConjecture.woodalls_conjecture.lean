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
# Woodall's conjecture

Let $D = (V, A)$ be a finite directed graph. Parallel and opposite arcs are allowed, loops are
not. For a vertex set $U \subseteq V$ let $\delta^+(U)$ be the set of arcs with tail in $U$ and
head outside $U$, and let $\delta^-(U)$ be the set of arcs with head in $U$ and tail outside $U$.

A *dicut* is an arc set $\delta^+(U)$ where $U$ is a nonempty proper subset of $V$ with
$\delta^-(U) = \emptyset$, that is, all arcs crossing the partition $(U, V \setminus U)$ do so in
the same direction. A *dijoin* is a set of arcs that intersects every dicut (equivalently, a set of
arcs whose contraction produces a strongly connected digraph).

**Woodall's conjecture** (1976): in every finite directed graph, the minimum number of arcs in a
dicut is equal to the maximum number of pairwise disjoint dijoins.

The inequality $\max \le \min$ is trivial: pairwise disjoint dijoins must each use a different arc
of a minimum dicut. The content of the conjecture is that a digraph whose minimum dicut has
$\tau$ arcs always has $\tau$ pairwise disjoint dijoins.

The conjecture is only meaningful for digraphs that have a dicut, i.e. digraphs with at least two
vertices that are not strongly connected. In a digraph without dicuts the minimum is undefined
and every arc set is a dijoin.

A finite directed graph $D = (V, A)$ is given by a finite type `V` of vertices, a finite type `A`
of arcs and maps `tail head : A → V` sending an arc to its tail and head. This representation
allows parallel and opposite arcs.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Woodall%27s_conjecture)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- D. R. Woodall, *Menger and König systems*, in: Theory and Applications of Graphs
  (Kalamazoo, 1976), Lecture Notes in Mathematics 642, Springer (1978), 620–635.
- [arXiv:2202.00392](https://arxiv.org/abs/2202.00392) A. Abdi, G. Cornuéjols, M. Zlatin,
  *On packing dijoins in digraphs and weighted digraphs*.
- A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer (2003),
  Chapter 56.
-/

namespace WoodallsConjecture

variable {V A : Type*} (tail head : A → V)

/-- The set $\delta^+(U)$ of arcs leaving the vertex set `U`: arcs with tail in `U` and head
outside `U`. -/
def outArcs (U : Set V) : Set A := {a | tail a ∈ U ∧ head a ∉ U}

/-- `U` is a nonempty proper subset of the vertices that no arc enters, i.e.
$\delta^-(U) = \emptyset$. Such a `U` determines the dicut $\delta^+(U)$. -/
def IsDicutShore (U : Set V) : Prop :=
  U.Nonempty ∧ Uᶜ.Nonempty ∧ ∀ a, head a ∈ U → tail a ∈ U

/-- A *dicut* is an arc set $\delta^+(U)$ where `U` is a nonempty proper subset of the vertices
with $\delta^-(U) = \emptyset$. -/
def IsDicut (C : Set A) : Prop :=
  ∃ U : Set V, IsDicutShore tail head U ∧ C = outArcs tail head U

/-- A *dijoin* is a set of arcs that intersects every dicut. -/
def IsDijoin (J : Set A) : Prop :=
  ∀ C, IsDicut tail head C → (J ∩ C).Nonempty

/-- The set of sizes of dicuts of the digraph. -/
def dicutSizes : Set ℕ := {n | ∃ C, IsDicut tail head C ∧ C.ncard = n}

/-- The set of natural numbers `n` such that the digraph has `n` pairwise disjoint dijoins. -/
def dijoinPackingSizes : Set ℕ :=
  {n | ∃ J : Fin n → Set A,
    (∀ i, IsDijoin tail head (J i)) ∧ Pairwise fun i j ↦ Disjoint (J i) (J j)}

/-- **Woodall's conjecture.** Let $D = (V, A)$ be a finite directed graph without loops
(parallel and opposite arcs are allowed) that has at least one dicut, and let $\tau$ be the
minimum number of arcs in a dicut of $D$. Then $\tau$ is the maximum number of pairwise disjoint
dijoins of $D$: there are $\tau$ pairwise disjoint dijoins, and no more.

The hypothesis `hτ` requires that `D` has a dicut. This excludes the degenerate case of strongly
connected digraphs and digraphs with at most one vertex, where the minimum is undefined. -/
theorem woodalls_conjecture [Finite V] [Finite A]
    (hloop : ∀ a, tail a ≠ head a) (τ : ℕ) (hτ : IsLeast (dicutSizes tail head) τ) :
    IsGreatest (dijoinPackingSizes tail head) τ := by
  sorry

end WoodallsConjecture

theorem WoodallsConjecture.woodalls_conjecture.disproof : ¬ (type_of% @WoodallsConjecture.woodalls_conjecture) := sorry
