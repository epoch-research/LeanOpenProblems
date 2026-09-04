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
# Walescki's theorem for hypergraphs

Walecki's theorem (reported by Lucas in 1892) states that the complete graph $K_n$ on an odd
number $n$ of vertices has a *Hamiltonian decomposition*: its edge set can be partitioned into
Hamiltonian cycles. The hypergraph analogue asks the same question for the complete $k$-uniform
hypergraph $K_n^{(k)}$ (all $k$-subsets of an $n$-set), with Hamiltonian cycles replaced by
*tight Hamilton cycles*: a cyclic ordering $v_0, \dots, v_{n-1}$ of all $n$ vertices, whose edges
are the $n$ sets $\{v_i, v_{i+1}, \dots, v_{i+k-1}\}$ (indices mod $n$) of $k$ cyclically
consecutive vertices.

Since a tight Hamilton cycle on $n > k$ vertices has exactly $n$ edges, such a decomposition can
only exist when $n$ divides $\binom{n}{k}$, equivalently when $k$ divides $\binom{n-1}{k-1}$ (the
number of cycles in the decomposition is then $\binom{n-1}{k-1}/k$). The question, formulated by
Bailey and Stevens (and, for $n \ge n_0(k)$, the tight case $\ell = k - 1$ of a conjecture of Kühn
and Osthus), is whether this necessary condition is also sufficient. For $k = 2$ this is Walecki's
theorem. The analogous statement for Hamilton *Berge* cycles is known: it was proved by Kühn and
Osthus for $k \ge 4$ and $n \ge 30$, and follows from results of Bermond and Verrall for $k = 3$.

*References:*
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia: Hamiltonian decomposition, Uniform hypergraphs](https://en.wikipedia.org/wiki/Hamiltonian_decomposition%23Uniform_Hypergraphs)
- [BS10] R. Bailey, B. Stevens, *Hamiltonian decompositions of complete $k$-uniform hypergraphs*,
  Discrete Math. 310 (2010), 3088–3095. DOI: 10.1016/j.disc.2009.03.047
- [KO14] D. Kühn, D. Osthus, *Decompositions of complete uniform hypergraphs into Hamilton Berge
  cycles*, J. Combin. Theory Ser. A 126 (2014), 128–135.
  [arXiv:1403.7932](https://arxiv.org/abs/1403.7932)
-/

namespace WalesckisTheoremForHypergraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A cyclic ordering of the vertices of a finite type `V` is encoded by its successor map: a
permutation `σ` of `V` that is a single cycle moving every vertex. The **tight Hamilton cycle**
determined by `σ` in the complete `k`-uniform hypergraph on `V` has as its edges the sets
`{v, σ v, …, σ^(k-1) v}` of `k` cyclically consecutive vertices, one for each starting
vertex `v`. -/
def tightHamiltonCycle (σ : Equiv.Perm V) (k : ℕ) : Finset (Finset V) :=
  Finset.univ.image fun v => (Finset.range k).image fun j => (σ ^ j) v

/-- `C` is the edge set of a tight Hamilton cycle of the complete `k`-uniform hypergraph on `V`:
there is a cyclic ordering of all the vertices of `V` (a permutation `σ` that is a single cycle
moving every vertex) whose sets of `k` cyclically consecutive vertices are exactly the edges
of `C`. -/
def IsTightHamiltonCycle (k : ℕ) (C : Finset (Finset V)) : Prop :=
  ∃ σ : Equiv.Perm V, σ.IsCycle ∧ σ.support = Finset.univ ∧ C = tightHamiltonCycle σ k

@[category API, AMS 5]
theorem mem_tightHamiltonCycle {σ : Equiv.Perm V} {k : ℕ} {e : Finset V} :
    e ∈ tightHamiltonCycle σ k ↔ ∃ v, e = (Finset.range k).image fun j => (σ ^ j) v := by
  simp [tightHamiltonCycle, eq_comm]

/-- A tight Hamilton cycle has at most one edge per starting vertex. -/
@[category API, AMS 5]
theorem card_tightHamiltonCycle_le (σ : Equiv.Perm V) (k : ℕ) :
    (tightHamiltonCycle σ k).card ≤ Fintype.card V :=
  (Finset.card_image_le).trans_eq (Finset.card_univ)

/-- If `σ` is a cyclic ordering of all of `V` and `k ≤ |V|`, then every edge of the tight
Hamilton cycle determined by `σ` has exactly `k` vertices, i.e. it is an edge of the complete
`k`-uniform hypergraph on `V`. -/
@[category test, AMS 5]
theorem tightHamiltonCycle_subset_powersetCard {σ : Equiv.Perm V} (hσ : σ.IsCycle)
    (hsupp : σ.support = Finset.univ) {k : ℕ} (hk : k ≤ Fintype.card V) :
    tightHamiltonCycle σ k ⊆ Finset.univ.powersetCard k := by
  intro e he
  obtain ⟨v, rfl⟩ := mem_tightHamiltonCycle.mp he
  rw [Finset.mem_powersetCard]
  refine ⟨Finset.subset_univ _, ?_⟩
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj hij
  by_contra hne
  wlog hlt : i < j generalizing i j
  · exact this hij.symm hj hi (Ne.symm hne) (by omega)
  have h1 : (σ ^ (j - i)) ((σ ^ i) v) = (σ ^ i) v := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hlt.le, hij]
  have h2 : σ ^ (j - i) = 1 := by
    rw [hσ.pow_eq_one_iff]
    refine ⟨(σ ^ i) v, ?_, h1⟩
    have : (σ ^ i) v ∈ σ.support := by rw [hsupp]; exact Finset.mem_univ _
    exact Equiv.Perm.mem_support.mp this
  have h3 : orderOf σ ∣ j - i := orderOf_dvd_of_pow_eq_one h2
  rw [hσ.orderOf, hsupp, Finset.card_univ] at h3
  have := Nat.le_of_dvd (by omega) h3
  omega

/-- For `k = 1` the tight Hamilton cycle consists of all singletons, whatever the ordering. -/
@[category test, AMS 5]
theorem tightHamiltonCycle_one (σ : Equiv.Perm V) :
    tightHamiltonCycle σ 1 = Finset.univ.image ({·}) := by
  simp [tightHamiltonCycle]

/-- The natural cyclic ordering of `Fin 5` gives a tight Hamilton cycle of `K_5^{(2)}` with
`5` edges, a proper subgraph of `K_5`. -/
@[category test, AMS 5]
theorem card_tightHamiltonCycle_finRotate_five_two :
    (tightHamiltonCycle (finRotate 5) 2).card = 5 := by
  decide

/-- The complete graph `K_3` is itself a tight Hamilton cycle, so `K_3^{(2)}` is decomposed by
a single tight Hamilton cycle. -/
@[category test, AMS 5]
theorem isTightHamiltonCycle_three_two :
    IsTightHamiltonCycle 2 ((Finset.univ : Finset (Fin 3)).powersetCard 2) :=
  ⟨finRotate 3, isCycle_finRotate, support_finRotate, by decide⟩

/-- The complete `3`-uniform hypergraph `K_4^{(3)}` is itself a tight Hamilton cycle. -/
@[category test, AMS 5]
theorem isTightHamiltonCycle_four_three :
    IsTightHamiltonCycle 3 ((Finset.univ : Finset (Fin 4)).powersetCard 3) :=
  ⟨finRotate 4, isCycle_finRotate, support_finRotate, by decide⟩

/-- The two forms of the necessary divisibility condition agree: for `1 ≤ k ≤ n`, `n` divides
`n.choose k` if and only if `k` divides `(n - 1).choose (k - 1)`. -/
@[category API, AMS 5 11]
theorem dvd_choose_iff {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    n ∣ n.choose k ↔ k ∣ (n - 1).choose (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [← Nat.mul_dvd_mul_iff_right (Nat.succ_pos l), ← Nat.add_one_mul_choose_eq,
    Nat.mul_dvd_mul_iff_left (Nat.succ_pos m)]

/--
**Walescki's theorem for hypergraphs** (Bailey–Stevens conjecture; the tight case $\ell = k - 1$
of a conjecture of Kühn and Osthus).

Do complete $k$-uniform hypergraphs admit Hamiltonian decompositions into tight cycles? That is:
for all $k \ge 2$ and $n > k$ such that $n$ divides $\binom{n}{k}$ (the obvious necessary
condition, since a tight Hamilton cycle has exactly $n$ edges; equivalently $k$ divides
$\binom{n-1}{k-1}$), can the edge set of the complete $k$-uniform hypergraph $K_n^{(k)}$ be
partitioned into tight Hamilton cycles? Here a tight Hamilton cycle is given by a cyclic ordering
of all $n$ vertices, and its edges are the $n$ sets of $k$ cyclically consecutive vertices.

Following the Wikipedia formulation and [BS10], no lower bound on $n$ beyond $n > k$ is assumed.
-/
@[category research open, AMS 5]
theorem walesckis_theorem_for_hypergraphs :
    answer(sorry) ↔ ∀ k n : ℕ, 2 ≤ k → k < n → n ∣ n.choose k →
      ∃ P : Finpartition ((Finset.univ : Finset (Fin n)).powersetCard k),
        ∀ C ∈ P.parts, IsTightHamiltonCycle k C := by
  sorry

end WalesckisTheoremForHypergraphs
