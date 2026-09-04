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
# Perfect 1-factorization conjecture

A *1-factor* of a graph is a perfect matching. A *1-factorization* of a graph is a partition
of its edge set into 1-factors. A pair of 1-factors of a 1-factorization is a *perfect pair* if
their union is a Hamiltonian cycle, and a 1-factorization is *perfect* if every pair of its
1-factors is a perfect pair.

In 1964 Anton Kotzig conjectured that every complete graph $K_{2n}$ with $n \geq 2$ has a
perfect 1-factorization.

*References:*
- [Wikipedia, Graph factorization](https://en.wikipedia.org/wiki/Graph_factorization%23Perfect_1-factorization)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
-/

namespace Perfect1FactorizationConjecture

open SimpleGraph

variable {V ι : Type*} {G : SimpleGraph V}

/-- A family `F` of subgraphs of `G` indexed by `ι` is a *1-factorization* of `G` if every `F i`
is a 1-factor of `G` (i.e. a perfect matching) and every edge of `G` lies in exactly one `F i`. -/
def IsOneFactorization (G : SimpleGraph V) (F : ι → G.Subgraph) : Prop :=
  (∀ i, (F i).IsPerfectMatching) ∧ ∀ e ∈ G.edgeSet, ∃! i, e ∈ (F i).edgeSet

/-- Distinct 1-factors of a 1-factorization are edge-disjoint. -/
@[category API, AMS 5]
theorem IsOneFactorization.disjoint_edgeSet {F : ι → G.Subgraph} (hF : IsOneFactorization G F)
    {i j : ι} (hij : i ≠ j) : Disjoint (F i).edgeSet (F j).edgeSet := by
  rw [Set.disjoint_left]
  intro e hi hj
  obtain ⟨k, -, hk⟩ := hF.2 e ((F i).edgeSet_subset hi)
  exact hij ((hk i hi).trans (hk j hj).symm)

variable [DecidableEq V]

/-- A 1-factorization `F` of `G` is *perfect* if the union of any two distinct 1-factors `F i`
and `F j` is a Hamiltonian cycle of `G`. -/
def IsPerfectOneFactorization (G : SimpleGraph V) (F : ι → G.Subgraph) : Prop :=
  IsOneFactorization G F ∧
    ∀ i j, i ≠ j →
      ∃ (a : V) (p : G.Walk a a), p.IsHamiltonianCycle ∧ p.toSubgraph = F i ⊔ F j

/-- **Perfect 1-factorization conjecture** (Kotzig, 1964).

Every complete graph on an even number of vertices admits a perfect 1-factorization. That is, for
every $n \geq 2$ the edges of the complete graph $K_{2n}$ can be partitioned into $2n - 1$
perfect matchings such that the union of any two of these perfect matchings is a Hamiltonian
cycle.

The restriction $n \geq 2$ excludes the degenerate complete graphs $K_0$ and $K_2$, which have
fewer than two 1-factors in any 1-factorization, so that the condition on pairs of 1-factors
is vacuous for them. -/
@[category research open, AMS 5]
theorem perfect_1_factorization_conjecture (n : ℕ) (hn : 2 ≤ n) :
    ∃ F : Fin (2 * n - 1) → (⊤ : SimpleGraph (Fin (2 * n))).Subgraph,
      IsPerfectOneFactorization ⊤ F := by
  sorry

/-- The empty family is a perfect 1-factorization of the empty graph on no vertices. -/
@[category test, AMS 5]
theorem isPerfectOneFactorization_isEmpty [IsEmpty V] [IsEmpty ι] (F : ι → G.Subgraph) :
    IsPerfectOneFactorization G F := by
  refine ⟨⟨fun i => isEmptyElim i, fun e he => ?_⟩, fun i => isEmptyElim i⟩
  induction e using Sym2.ind with
  | h x _ => exact isEmptyElim x

/- The complete graph `K_4` has a unique 1-factorization, consisting of the three 1-factors
`{01, 23}`, `{02, 13}` and `{03, 12}`, and it is perfect. -/
section K4

/-- The `k`-th 1-factor of `K_4`: it pairs each vertex `a` with `a XOR (k + 1)`. -/
def k4Factor (k : Fin 3) : (⊤ : SimpleGraph (Fin 4)).Subgraph where
  verts := Set.univ
  Adj a b := a.val ^^^ b.val = k.val + 1
  adj_sub {a b} h := by
    revert h
    fin_cases k <;> fin_cases a <;> fin_cases b <;> decide
  edge_vert _ := Set.mem_univ _
  symm a b h := by
    show b.val ^^^ a.val = k.val + 1
    rw [Nat.xor_comm]
    exact h

instance (k : Fin 3) : DecidableRel (k4Factor k).Adj :=
  fun a b => inferInstanceAs (Decidable (a.val ^^^ b.val = k.val + 1))

/-- The 4-cycle `a → b → c → d → a` in `K_4`. -/
def k4Cycle (a b c d : Fin 4) (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a) :
    (⊤ : SimpleGraph (Fin 4)).Walk a a :=
  .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))

@[category API, AMS 5]
theorem isHamiltonianCycle_k4Cycle {a b c d : Fin 4} {hab : a ≠ b} {hbc : b ≠ c} {hcd : c ≠ d}
    {hda : d ≠ a} (h₁ : (k4Cycle a b c d hab hbc hcd hda).edges.Nodup)
    (h₂ : (k4Cycle a b c d hab hbc hcd hda).support.tail.Nodup)
    (h₃ : ∀ v, (k4Cycle a b c d hab hbc hcd hda).support.tail.count v = 1) :
    (k4Cycle a b c d hab hbc hcd hda).IsHamiltonianCycle := by
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one, Walk.isCycle_def,
    Walk.isTrail_def]
  exact ⟨⟨h₁, by simp [k4Cycle], h₂⟩, h₃⟩

@[category test, AMS 5]
theorem isOneFactorization_k4Factor : IsOneFactorization ⊤ k4Factor := by
  refine ⟨fun k => ?_, fun e he => ?_⟩
  · rw [Subgraph.isPerfectMatching_iff]
    intro v
    unfold ExistsUnique
    fin_cases k <;> fin_cases v <;> decide
  · induction e using Sym2.ind with
    | h a b =>
      simp only [Subgraph.mem_edgeSet]
      simp only [mem_edgeSet, top_adj] at he
      revert he
      unfold ExistsUnique
      fin_cases a <;> fin_cases b <;> decide

@[category test, AMS 5]
theorem k4Factor_perfectPair_zero_one : ∃ (a : Fin 4) (p : (⊤ : SimpleGraph (Fin 4)).Walk a a),
    p.IsHamiltonianCycle ∧ p.toSubgraph = k4Factor 0 ⊔ k4Factor 1 := by
  refine ⟨0, k4Cycle 0 1 3 2 (by decide) (by decide) (by decide) (by decide),
    isHamiltonianCycle_k4Cycle (by decide) (by decide) (by decide), ?_⟩
  ext v w
  · fin_cases v <;> simp [k4Cycle, k4Factor]
  · fin_cases v <;> fin_cases w <;> simp [k4Cycle, k4Factor]

@[category test, AMS 5]
theorem k4Factor_perfectPair_zero_two : ∃ (a : Fin 4) (p : (⊤ : SimpleGraph (Fin 4)).Walk a a),
    p.IsHamiltonianCycle ∧ p.toSubgraph = k4Factor 0 ⊔ k4Factor 2 := by
  refine ⟨0, k4Cycle 0 1 2 3 (by decide) (by decide) (by decide) (by decide),
    isHamiltonianCycle_k4Cycle (by decide) (by decide) (by decide), ?_⟩
  ext v w
  · fin_cases v <;> simp [k4Cycle, k4Factor]
  · fin_cases v <;> fin_cases w <;> simp [k4Cycle, k4Factor]

@[category test, AMS 5]
theorem k4Factor_perfectPair_one_two : ∃ (a : Fin 4) (p : (⊤ : SimpleGraph (Fin 4)).Walk a a),
    p.IsHamiltonianCycle ∧ p.toSubgraph = k4Factor 1 ⊔ k4Factor 2 := by
  refine ⟨0, k4Cycle 0 2 1 3 (by decide) (by decide) (by decide) (by decide),
    isHamiltonianCycle_k4Cycle (by decide) (by decide) (by decide), ?_⟩
  ext v w
  · fin_cases v <;> simp [k4Cycle, k4Factor]
  · fin_cases v <;> fin_cases w <;> simp [k4Cycle, k4Factor]

/-- The 1-factorization `k4Factor` of `K_4` is perfect. In particular the perfect
1-factorization conjecture holds for `n = 2`. -/
@[category test, AMS 5]
theorem isPerfectOneFactorization_k4Factor : IsPerfectOneFactorization ⊤ k4Factor := by
  refine ⟨isOneFactorization_k4Factor, fun i j hij => ?_⟩
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact k4Factor_perfectPair_zero_one
  · exact k4Factor_perfectPair_zero_two
  · exact sup_comm (k4Factor 0) (k4Factor 1) ▸ k4Factor_perfectPair_zero_one
  · exact absurd rfl hij
  · exact k4Factor_perfectPair_one_two
  · exact sup_comm (k4Factor 0) (k4Factor 2) ▸ k4Factor_perfectPair_zero_two
  · exact sup_comm (k4Factor 1) (k4Factor 2) ▸ k4Factor_perfectPair_one_two
  · exact absurd rfl hij

end K4

end Perfect1FactorizationConjecture
