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
# Ryser's conjecture

Ryser's conjecture relates the maximum matching size $\nu(H)$ and the minimum transversal
(vertex cover) size $\tau(H)$ of a finite hypergraph $H$. It asserts that every $r$-partite
$r$-uniform hypergraph $H$ satisfies
$$\tau(H) \le (r-1)\,\nu(H).$$
The conjecture first appeared in the 1971 Ph.D. thesis of J. R. Henderson, a student of Ryser.
It is known for $r = 2$ (Kőnig's theorem) and $r = 3$ (Aharoni), and open for every $r \ge 4$.

Mathlib has no general hypergraph API, so a finite hypergraph on a finite vertex type `V` is
represented here by its finite set of hyperedges `H : Finset (Finset V)`.

*References:*
- [Wikipedia: Ryser's conjecture](https://en.wikipedia.org/wiki/Ryser%27s_conjecture)
- [Wikipedia: List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [ABPS18] A. Abu-Khazneh, J. Barát, A. Pokrovskiy, T. Szabó, *A family of extremal hypergraphs
  for Ryser's conjecture*. arXiv:1605.06361 (2018), Conjecture 1.
- [Ah01] R. Aharoni, *Ryser's Conjecture for Tripartite 3-Graphs*. Combinatorica 21 (2001), 1–4.
-/

namespace RysersConjecture

variable {V : Type*}

/-- A **matching** `M` of the hypergraph `H` is a set of hyperedges of `H` such that each vertex
appears in at most one of them, i.e. a set of pairwise disjoint hyperedges of `H`. -/
def IsMatching (H M : Finset (Finset V)) : Prop :=
  M ⊆ H ∧ (M : Set (Finset V)).PairwiseDisjoint id

/-- A **transversal** (or vertex cover) `T` of the hypergraph `H` is a set of vertices such that
each hyperedge of `H` contains at least one vertex of `T`. -/
def IsTransversal (H : Finset (Finset V)) (T : Finset V) : Prop :=
  ∀ e ∈ H, ∃ v ∈ T, v ∈ e

/-- The **matching number** $\nu(H)$ of the hypergraph `H`: the largest size of a matching of `H`.
The set of matching sizes is nonempty (the empty matching) and bounded by `H.card`, so the
supremum is attained. -/
noncomputable def matchingNumber (H : Finset (Finset V)) : ℕ :=
  sSup {k | ∃ M, IsMatching H M ∧ M.card = k}

/-- The **transversal number** $\tau(H)$ of the hypergraph `H`: the smallest size of a transversal
of `H`. If `H` has no empty hyperedge (e.g. if `H` is `r`-uniform with `r ≥ 1`) then transversals
exist and the infimum is attained. -/
noncomputable def transversalNumber (H : Finset (Finset V)) : ℕ :=
  sInf {k | ∃ T, IsTransversal H T ∧ T.card = k}

/-- The hypergraph `H` is **`r`-uniform** if each hyperedge has exactly `r` vertices. -/
def IsUniform (r : ℕ) (H : Finset (Finset V)) : Prop :=
  ∀ e ∈ H, e.card = r

/-- The hypergraph `H` is **`r`-partite** if its vertices can be partitioned into `r` sets (the
fibres of a map `f : V → Fin r`) so that every hyperedge contains exactly one element of each of
these sets. Fibres may be empty; an empty fibre forces `H` to have no hyperedges. -/
def IsPartite (r : ℕ) (H : Finset (Finset V)) : Prop :=
  ∃ f : V → Fin r, ∀ e ∈ H, ∀ i : Fin r, ∃! v, v ∈ e ∧ f v = i

/--
**Ryser's conjecture.** Let $r \ge 2$ and let $H$ be a finite $r$-partite $r$-uniform hypergraph,
i.e. every hyperedge has exactly $r$ vertices and the vertex set can be partitioned into $r$ sets
so that every hyperedge contains exactly one element of each set. Then the minimum transversal
size and the maximum matching size of $H$ satisfy
$$\tau(H) \le (r-1)\,\nu(H).$$

For every $r$-uniform hypergraph one has $\tau(H) \le r\,\nu(H)$; the conjecture says that for
$r$-partite hypergraphs the factor $r$ can be decreased by $1$.

The restriction $r \ge 2$ is the implicit convention of the sources: for $r = 1$ the inequality
fails for every nonempty $1$-uniform hypergraph (see `rysers_conjecture.variants.one_false`), and
for $r = 0$ the only possible hyperedge is $\emptyset$, which has no transversal. The uniformity
hypothesis is implied by `IsPartite` (see `IsPartite.isUniform`) and is kept to mirror the phrase
"$r$-partite $r$-uniform". The case $r = 2$ is Kőnig's theorem and the case $r = 3$ was proved by
Aharoni [Ah01]; the conjecture is open for every $r \ge 4$.
-/
theorem rysers_conjecture [Fintype V] (r : ℕ) (hr : 2 ≤ r) (H : Finset (Finset V))
    (hH : IsUniform r H) (hH' : IsPartite r H) :
    transversalNumber H ≤ (r - 1) * matchingNumber H := by
  sorry

end RysersConjecture

theorem RysersConjecture.rysers_conjecture.disproof : ¬ (type_of% @RysersConjecture.rysers_conjecture) := sorry
