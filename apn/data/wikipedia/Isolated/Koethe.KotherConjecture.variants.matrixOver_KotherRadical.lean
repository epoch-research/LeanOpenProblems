/-
Copyright 2025 The Formal Conjectures Authors.

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
# Köthe conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/K%C3%B6the_conjecture)
-/

open Ideal TwoSidedIdeal Polynomial

open Matrix

universe u v w

variable {R : Type*}

variable [Ring R]

namespace Koethe

/-- Say a subset `I` of a ring `R` is nilpotent if all its elements are nilpotent. -/
def IsNil {S : Type*} [SetLike S R] (I : S) := ∀ i ∈ I, IsNilpotent i

-- TODO(lezeau): add some basic API and already known results for nil ideals

variable (R) in
/-- The *Kothe Radical* of a ring `R` is the sum of all (two-sided) nil ideals of `R`.
Tags: Kothe Radical, upper nilradical-/
def KotheRadical : TwoSidedIdeal R := sSup {I : TwoSidedIdeal R | IsNil I}

-- This is often denoted `Nil*(R)`
local notation "Nil* " R => KotheRadical R

/- ### Basic API for nil ideals -/

open scoped Classical in
/-- The **Köthe conjecture**: for any finite index type `n`, the Köthe radical of the matrix
ring `M_n(R)` is the ideal `M_n(Nil*(R))` of matrices with entries in the Köthe radical of `R`. -/
theorem KotherConjecture.variants.matrixOver_KotherRadical (n : Type*) [Fintype n] :
    matrix n (Nil* R) = Nil* (Matrix n n R) := by
  sorry

/-
### Relations between the different formulations

All the formulations of the Köthe conjecture above are known to be equivalent (Krempa). We record
here the implications that have a short formal proof. In particular each of
`KotheConjecture`, `KotherConjecture.variants.le_KotherRadical`,
`KotherConjecture.variants.two_by_two_matrix` and
`KotherConjecture.variants.matrixOver_KotherRadical` implies
`KotherConjecture.variants.general_matrix`, so that a counterexample to the latter immediately
yields counterexamples to all the others.

The implication `KotherConjecture.variants.general_matrix → KotheConjecture` (also due to Krempa)
is not formalized here.
-/

section ColumnIdeal

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The left ideal of `Matrix n n R` consisting of the matrices with entries in `I` which are
supported on the `j`-th column. -/
def columnIdeal (I : TwoSidedIdeal R) (j : n) : Ideal (Matrix n n R) where
  carrier := {M | ∀ i k, M i k ∈ I ∧ (k ≠ j → M i k = 0)}
  zero_mem' _ _ := ⟨I.zero_mem, fun _ => rfl⟩
  add_mem' hM hN i k :=
    ⟨add_mem (hM i k).1 (hN i k).1, fun hk => by simp [(hM i k).2 hk, (hN i k).2 hk]⟩
  smul_mem' B _ hM i k := by
    simp only [smul_eq_mul, Matrix.mul_apply]
    refine ⟨sum_mem fun l _ => I.mul_mem_left _ _ (hM l k).1, fun hk => ?_⟩
    exact Finset.sum_eq_zero fun l _ => by rw [(hM l k).2 hk, mul_zero]

end ColumnIdeal

section MatrixTransfer

variable {m : Type*} [Fintype m] [DecidableEq m] {n : Type*} [Fintype n] [DecidableEq n]

end MatrixTransfer

/-
TODO(lezeau): The two last statements I want to formalize use the (two-sided) Jacobson ideal.
Sanity check that the current mathlib definition is what I want.
-/

end Koethe

theorem Koethe.KotherConjecture.variants.matrixOver_KotherRadical.disproof : ¬ (type_of% @Koethe.KotherConjecture.variants.matrixOver_KotherRadical) := sorry
