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
# Isomorphism problem of Coxeter groups

It is an unresolved problem in group theory to determine whether or not two Coxeter groups
(specified by their Coxeter diagrams, or equivalently by their Coxeter matrices) are isomorphic as
abstract groups. Equivalently, the problem asks to determine, for a given Coxeter group $W$, the
possible subsets $S$ of $W$ that are Coxeter generating sets for $W$ (that is, for which $(W, S)$
is a Coxeter system).

As in the literature (Problem 1 of Mühlherr's survey, the "classic isomorphism problem" of
Santos Rego and Schwer), this is a decision problem about finitely generated Coxeter groups: is
there an algorithm which, given two Coxeter matrices $M$ and $M'$ of finite rank, decides whether
the Coxeter groups $W(M)$ and $W(M')$ are isomorphic? The expected answer is "yes", but the problem
is open.

## Implementation notes

A Coxeter matrix of finite rank is a `CoxeterMatrix (Fin n)` for some `n : ℕ`; every Coxeter
matrix over a finite index type is a reindexing of one of these, and reindexing does not change
the Coxeter group up to isomorphism (`CoxeterMatrix.reindexGroupEquiv`). Mathlib encodes the entry
$\infty$ of a Coxeter matrix as `0`.

Decidability is expressed with Mathlib's `ComputablePred`, which requires a `Primcodable` encoding
of the inputs. We encode a finite-rank Coxeter matrix by its table of entries, a `List (List ℕ)`,
and transport the resulting `Primcodable` instance to the type
`FinCoxeterMatrix := Σ n, CoxeterMatrix (Fin n)` along an explicit bijection.

*References:*
- [Wikipedia, *Isomorphism problem of Coxeter groups*](https://en.wikipedia.org/wiki/Isomorphism_problem_of_Coxeter_groups)
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [B. Mühlherr, *The isomorphism problem for Coxeter groups*](https://arxiv.org/abs/math/0506572),
  Problems 1 and 3.
- [Y. Santos Rego, P. Schwer, *The galaxy of Coxeter groups*](https://arxiv.org/abs/2211.17038),
  Section 3.2, "The (classic) isomorphism problem".
-/

namespace IsomorphismProblemOfCoxeterGroups

open Primrec

/-- A Coxeter matrix of finite rank, indexed by `Fin n` for some `n : ℕ`. -/
abbrev FinCoxeterMatrix := Σ n : ℕ, CoxeterMatrix (Fin n)

section Encoding

/-- The `(i, j)`-entry of a table `L : List (List ℕ)` (with default value `0`). -/
def entry (L : List (List ℕ)) (i j : ℕ) : ℕ := (L.getD i []).getD j 0

/-- A table `L : List (List ℕ)` is a *Coxeter table* if it is square, symmetric, and its
`(i, j)`-entry equals `1` exactly when `i = j`. These are precisely the tables of entries of
finite-rank Coxeter matrices, see `equivTable`. -/
def IsCoxeterTable (L : List (List ℕ)) : Prop :=
  (∀ row ∈ L, row.length = L.length) ∧
    ∀ i < L.length, ∀ j < L.length, entry L i j = entry L j i ∧ (i = j ↔ entry L i j = 1)

instance : DecidablePred IsCoxeterTable := fun L => by
  unfold IsCoxeterTable; infer_instance

theorem primrec_entry :
    Primrec fun p : List (List ℕ) × (ℕ × ℕ) => entry p.1 p.2.1 p.2.2 :=
  (list_getD 0).comp ((list_getD ([] : List ℕ)).comp fst (fst.comp snd)) (snd.comp snd)

/-- Bounded universal quantification over `ℕ` preserves primitive recursive relations. This
generalises `PrimrecRel.forall_lt` from relations on `ℕ × ℕ` to relations on `ℕ × β`. -/
theorem primrecRel_forall_lt {β : Type*} [Primcodable β] {R : ℕ → β → Prop}
    (hR : PrimrecRel R) : PrimrecRel fun (n : ℕ) (b : β) => ∀ x < n, R x b :=
  PrimrecPred.of_eq ((PrimrecRel.forall_mem_list hR).comp (list_range.comp fst) snd) fun _ => by
    simp

/-- Being a Coxeter table is primitive recursive, so that Coxeter tables form a `Primcodable`
type. -/
theorem primrecPred_isCoxeterTable : PrimrecPred IsCoxeterTable := by
  have h₁ : PrimrecPred fun L : List (List ℕ) => ∀ row ∈ L, row.length = L.length :=
    (PrimrecRel.forall_mem_list (R := fun (row : List ℕ) (L : List (List ℕ)) =>
      row.length = L.length) (Primrec.eq.comp (list_length.comp fst) (list_length.comp snd))).comp
      .id .id
  have e₁ : Primrec fun p : ℕ × (ℕ × List (List ℕ)) => entry p.2.2 p.2.1 p.1 :=
    primrec_entry.comp ((snd.comp snd).pair ((fst.comp snd).pair fst))
  have e₂ : Primrec fun p : ℕ × (ℕ × List (List ℕ)) => entry p.2.2 p.1 p.2.1 :=
    primrec_entry.comp ((snd.comp snd).pair (fst.pair (fst.comp snd)))
  have hij : PrimrecPred fun p : ℕ × (ℕ × List (List ℕ)) => p.2.1 = p.1 :=
    Primrec.eq.comp (fst.comp snd) fst
  have h1 : PrimrecPred fun p : ℕ × (ℕ × List (List ℕ)) => entry p.2.2 p.2.1 p.1 = 1 :=
    Primrec.eq.comp e₁ (const 1)
  have h₀ : PrimrecRel fun (j : ℕ) (q : ℕ × List (List ℕ)) =>
      entry q.2 q.1 j = entry q.2 j q.1 ∧ (q.1 = j ↔ entry q.2 q.1 j = 1) :=
    (Primrec.eq.comp e₁ e₂).and (((hij.and h1).or (hij.not.and h1.not)).of_eq fun _ =>
      iff_iff_and_or_not_and_not.symm)
  have h₂ : PrimrecRel fun (i : ℕ) (L : List (List ℕ)) => ∀ j < L.length,
      entry L i j = entry L j i ∧ (i = j ↔ entry L i j = 1) :=
    (primrecRel_forall_lt h₀).comp (list_length.comp snd) (fst.pair snd)
  exact h₁.and ((primrecRel_forall_lt h₂).comp list_length .id)

/-- The table of entries of a finite-rank Coxeter matrix, as a list of rows. -/
def toTable {n : ℕ} (M : CoxeterMatrix (Fin n)) : List (List ℕ) :=
  List.ofFn fun i => List.ofFn fun j => M i j

theorem length_toTable {n : ℕ} (M : CoxeterMatrix (Fin n)) : (toTable M).length = n :=
  List.length_ofFn

theorem entry_toTable {n : ℕ} (M : CoxeterMatrix (Fin n)) (i j : Fin n) :
    entry (toTable M) i j = M i j := by
  simp [entry, toTable, i.2, j.2]

theorem isCoxeterTable_toTable {n : ℕ} (M : CoxeterMatrix (Fin n)) :
    IsCoxeterTable (toTable M) := by
  refine ⟨fun row hrow => ?_, fun i hi j hj => ?_⟩
  · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hrow
    simp [toTable]
  · rw [length_toTable] at hi hj
    rw [entry_toTable M ⟨i, hi⟩ ⟨j, hj⟩, entry_toTable M ⟨j, hj⟩ ⟨i, hi⟩]
    refine ⟨M.symmetric _ _, fun h => ?_, fun h => ?_⟩
    · subst h
      exact M.diagonal _
    · by_contra h'
      exact M.off_diagonal ⟨i, hi⟩ ⟨j, hj⟩ (fun e => h' (congrArg Fin.val e)) h

/-- The Coxeter matrix with a given Coxeter table of entries. -/
def ofTable (L : List (List ℕ)) (hL : IsCoxeterTable L) : CoxeterMatrix (Fin L.length) where
  M := Matrix.of fun i j => entry L i j
  isSymm := Matrix.IsSymm.ext fun i j => (hL.2 j j.2 i i.2).1
  diagonal i := (hL.2 i i.2 i i.2).2.mp rfl
  off_diagonal i j h h' := h (Fin.ext ((hL.2 i i.2 j j.2).2.mpr h'))

theorem sigma_mk_eq {m n : ℕ} (h : m = n) (X : CoxeterMatrix (Fin m)) (Y : CoxeterMatrix (Fin n))
    (hXY : ∀ i j : Fin m, X i j = Y (Fin.cast h i) (Fin.cast h j)) :
    (⟨m, X⟩ : FinCoxeterMatrix) = ⟨n, Y⟩ := by
  subst h
  congr
  ext i j
  exact hXY i j

/-- Finite-rank Coxeter matrices correspond bijectively to Coxeter tables. -/
def equivTable : FinCoxeterMatrix ≃ {L : List (List ℕ) // IsCoxeterTable L} where
  toFun M := ⟨toTable M.2, isCoxeterTable_toTable M.2⟩
  invFun L := ⟨L.1.length, ofTable L.1 L.2⟩
  left_inv := by
    rintro ⟨n, M⟩
    exact sigma_mk_eq (length_toTable M) _ _ fun i j =>
      entry_toTable M (Fin.cast (length_toTable M) i) (Fin.cast (length_toTable M) j)
  right_inv := by
    rintro ⟨L, hL⟩
    refine Subtype.ext (List.ext_getElem (length_toTable _) fun i h₁ h₂ => ?_)
    have hrow : L.length = L[i].length := (hL.1 _ (List.getElem_mem h₂)).symm
    refine List.ext_getElem (by simpa [toTable] using hrow) fun j h₃ h₄ => ?_
    simp [toTable, ofTable, entry, h₄]

/-- Finite-rank Coxeter matrices form a `Primcodable` type: a Coxeter matrix is encoded by its
table of entries. -/
instance : Primcodable FinCoxeterMatrix :=
  @Primcodable.ofEquiv _ _ (Primcodable.subtype primrecPred_isCoxeterTable) equivTable

end Encoding

/-- A subset `S` of a group `W` is a *Coxeter generating set of type `M`* for `W` if `(W, S)` is a
Coxeter system of type `M`, i.e. `S` is the set of simple reflections of some Coxeter system of
type `M` on `W`. -/
def IsCoxeterGeneratingSet {B W : Type*} [Group W] (M : CoxeterMatrix B) (S : Set W) : Prop :=
  ∃ cs : CoxeterSystem M W, Set.range cs.simple = S

/--
**Isomorphism problem of Coxeter groups, in terms of Coxeter generating sets.** Equivalently, the
problem asks to determine, for a given Coxeter group $W$, the possible subsets $S$ of $W$ that are
Coxeter generating sets for $W$ (that is, for which $(W, S)$ is a Coxeter system). The possible
Coxeter generating sets are described up to their type, i.e. the Coxeter matrix of the Coxeter
system $(W, S)$, which leads to the following decision problem: given finite-rank Coxeter matrices
$M$ and $M'$, decide whether the Coxeter group $W(M)$ has a Coxeter generating set $S$ such that
$(W(M), S)$ is a Coxeter system of type $M'$. Is there an algorithm solving this problem?
-/
theorem isomorphism_problem_of_coxeter_groups.variants.coxeter_generating_sets :
    ComputablePred fun p : FinCoxeterMatrix × FinCoxeterMatrix =>
      ∃ S : Set p.1.2.Group, IsCoxeterGeneratingSet p.2.2 S := by
  sorry

end IsomorphismProblemOfCoxeterGroups

theorem IsomorphismProblemOfCoxeterGroups.isomorphism_problem_of_coxeter_groups.variants.coxeter_generating_sets.disproof : ¬ (type_of% @IsomorphismProblemOfCoxeterGroups.isomorphism_problem_of_coxeter_groups.variants.coxeter_generating_sets) := sorry
