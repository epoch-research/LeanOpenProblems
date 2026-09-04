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
@[category research open, AMS 5]
theorem chvatals_toughness_conjecture :
    ∃ t : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      3 ≤ Fintype.card V → IsTough G t → G.IsHamiltonian := by
  sorry

/-- Every graph is `t`-tough for every `t ≤ 0`. -/
@[category API, AMS 5]
theorem isTough_of_nonpos [Finite V] (ht : t ≤ 0) : IsTough G t :=
  fun _ _ => (mul_nonpos_of_nonpos_of_nonneg ht (Nat.cast_nonneg _)).trans (Nat.cast_nonneg _)

/-- If `G` is `t`-tough then `G` is `s`-tough for every `s ≤ t`. -/
@[category API, AMS 5]
theorem IsTough.mono [Finite V] (hG : IsTough G t) (hst : s ≤ t) : IsTough G s :=
  fun S hS => (mul_le_mul_of_nonneg_right hst (Nat.cast_nonneg _)).trans (hG S hS)

/-- The complete graph is `t`-tough for every `t`. -/
@[category API, AMS 5]
theorem isTough_top [Finite V] (t : ℝ) : IsTough (⊤ : SimpleGraph V) t := fun S hS => by
  rw [induce_top] at hS
  have := preconnected_top.subsingleton_connectedComponent (V := ↥Sᶜ)
  exact absurd hS (not_lt.2 (Finite.card_le_one_iff_subsingleton.2 this))

/-- The edgeless graph on two vertices is not `t`-tough for any `t > 0`: removing no vertex
leaves two connected components. -/
@[category test, AMS 5]
theorem not_isTough_bot_fin_two (ht : 0 < t) : ¬ IsTough (⊥ : SimpleGraph (Fin 2)) t := by
  intro h
  have h2 : 1 < Nat.card
      ((⊥ : SimpleGraph (Fin 2)).induce (∅ : Set (Fin 2))ᶜ).ConnectedComponent := by
    rw [Finite.one_lt_card_iff_nontrivial]
    refine ⟨connectedComponentMk _ ⟨0, by simp⟩,
      connectedComponentMk _ ⟨1, by simp⟩, ?_⟩
    rw [Ne, ConnectedComponent.eq]
    simp [Subtype.ext_iff]
  have := h ∅ h2
  simp only [Set.ncard_empty, Nat.cast_zero] at this
  exact absurd this (not_le.2 (mul_pos ht (by exact_mod_cast zero_lt_one.trans h2)))

/-- The complete graph on two vertices is `t`-tough for every `t`, but it is not Hamiltonian,
since a cycle in a simple graph has at least three vertices. This is why the conjecture is
restricted to graphs with at least three vertices. -/
@[category test, AMS 5]
theorem not_isHamiltonian_top_fin_two : ¬ (⊤ : SimpleGraph (Fin 2)).IsHamiltonian := by
  intro h
  obtain ⟨a, p, hp⟩ := h (by simp)
  have h3 := hp.isCycle.three_le_length
  rw [hp.length_eq] at h3
  simp at h3

end ChvatalsToughnessConjecture
