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

/-- Every `r`-partite hypergraph (in the sense of `IsPartite`) is `r`-uniform. -/
@[category API, AMS 5]
theorem IsPartite.isUniform {r : ℕ} {H : Finset (Finset V)} (h : IsPartite r H) :
    IsUniform r H := by
  obtain ⟨f, hf⟩ := h
  intro e he
  rw [← Finset.card_fin r]
  refine Finset.card_bij (fun v _ => f v) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro v₁ hv₁ v₂ hv₂ hv
    obtain ⟨w, -, hw⟩ := hf e he (f v₁)
    exact (hw v₁ ⟨hv₁, rfl⟩).trans (hw v₂ ⟨hv₂, hv.symm⟩).symm
  · intro i _
    obtain ⟨v, ⟨hv, hvi⟩, -⟩ := hf e he i
    exact ⟨v, hv, hvi⟩

/-- The empty hypergraph has matching number `0`. -/
@[category test, AMS 5]
theorem matchingNumber_empty : matchingNumber (∅ : Finset (Finset V)) = 0 := by
  have : {k | ∃ M, IsMatching (∅ : Finset (Finset V)) M ∧ M.card = k} = {0} := by
    ext k
    constructor
    · rintro ⟨M, ⟨hM, -⟩, rfl⟩
      rw [Finset.subset_empty] at hM
      simp [hM]
    · rintro rfl
      exact ⟨∅, ⟨Finset.Subset.refl _, by simp⟩, by simp⟩
  simp [matchingNumber, this]

/-- The empty hypergraph has transversal number `0`. -/
@[category test, AMS 5]
theorem transversalNumber_empty : transversalNumber (∅ : Finset (Finset V)) = 0 := by
  refine Nat.sInf_eq_zero.mpr (Or.inl ⟨∅, ?_, by simp⟩)
  simp [IsTransversal]

/-- The hypergraph on two vertices with a single edge joining them has matching number `1`. -/
@[category test, AMS 5]
theorem matchingNumber_single_edge :
    matchingNumber ({{0, 1}} : Finset (Finset (Fin 2))) = 1 := by
  apply le_antisymm
  · refine csSup_le ⟨0, ∅, ⟨Finset.empty_subset _, by simp⟩, rfl⟩ ?_
    rintro k ⟨M, ⟨hM, -⟩, rfl⟩
    exact (Finset.card_le_card hM).trans (by simp)
  · refine le_csSup ⟨1, ?_⟩ ⟨{{0, 1}}, ⟨subset_rfl, by simp⟩, rfl⟩
    rintro k ⟨M, ⟨hM, -⟩, rfl⟩
    exact (Finset.card_le_card hM).trans (by simp)

/-- The hypergraph on two vertices with a single edge joining them has transversal number `1`. -/
@[category test, AMS 5]
theorem transversalNumber_single_edge :
    transversalNumber ({{0, 1}} : Finset (Finset (Fin 2))) = 1 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨{0}, fun e he => ⟨0, by simp, by simp_all⟩, rfl⟩
  · refine le_csInf ⟨1, {0}, fun e he => ⟨0, by simp, by simp_all⟩, rfl⟩ ?_
    rintro k ⟨T, hT, rfl⟩
    obtain ⟨v, hv, -⟩ := hT {0, 1} (by simp)
    exact Finset.card_pos.mpr ⟨v, hv⟩

/-- The hypergraph on two vertices with a single edge joining them is `2`-partite. -/
@[category test, AMS 5]
theorem isPartite_single_edge : IsPartite 2 ({{0, 1}} : Finset (Finset (Fin 2))) := by
  refine ⟨id, ?_⟩
  simp only [Finset.mem_singleton, forall_eq]
  intro i
  fin_cases i
  · exact ⟨0, by simp, fun v hv => hv.2⟩
  · exact ⟨1, by simp, fun v hv => hv.2⟩

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
@[category research open, AMS 5]
theorem rysers_conjecture [Fintype V] (r : ℕ) (hr : 2 ≤ r) (H : Finset (Finset V))
    (hH : IsUniform r H) (hH' : IsPartite r H) :
    transversalNumber H ≤ (r - 1) * matchingNumber H := by
  sorry

/-- The inequality of Ryser's conjecture fails for $r = 1$: the $1$-partite $1$-uniform
hypergraph with the single hyperedge $\{0\}$ has $\tau(H) = \nu(H) = 1 > 0 = (r-1)\,\nu(H)$.
This justifies the hypothesis $r \ge 2$ in `rysers_conjecture`. -/
@[category test, AMS 5]
theorem rysers_conjecture.variants.one_false :
    ∃ H : Finset (Finset (Fin 1)), IsUniform 1 H ∧ IsPartite 1 H ∧
      ¬ transversalNumber H ≤ (1 - 1) * matchingNumber H := by
  refine ⟨{{0}}, by simp [IsUniform], ⟨fun _ => 0, ?_⟩, ?_⟩
  · intro e he i
    simp only [Finset.mem_singleton] at he
    subst he
    exact ⟨0, by simp [Fin.ext_iff], fun v hv => by simp [Fin.ext_iff]⟩
  · simp only [Nat.sub_self, zero_mul, Nat.le_zero]
    rw [transversalNumber, Nat.sInf_eq_zero, not_or]
    refine ⟨?_, Set.Nonempty.ne_empty ⟨1, {0}, by simp [IsTransversal], by simp⟩⟩
    rintro ⟨T, hT, hT0⟩
    rw [Finset.card_eq_zero] at hT0
    subst hT0
    simp [IsTransversal] at hT

end RysersConjecture
