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
# Jónsson algebra

Does there exist a Jónsson algebra on $\aleph_\omega$?

Here an *algebra* is a set equipped with countably many finitary operations, that is, a model
for a first-order language with countably many function symbols and no relation symbols. A
*Jónsson algebra* is an algebra with no proper subalgebra of the same cardinality. A cardinal
$\kappa$ is a Jónsson cardinal if and only if there is no Jónsson algebra of cardinality
$\kappa$, so the question asks whether $\aleph_\omega$ fails to be a Jónsson cardinal.

*References:*
- [Wikipedia: List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia: Jónsson cardinal](https://en.wikipedia.org/wiki/J%C3%B3nsson_cardinal)
- Kanamori, A., *The Higher Infinite: Large Cardinals in Set Theory from Their Beginnings*,
  2nd ed., Springer (2003).
-/

open Cardinal Ordinal FirstOrder Language

namespace JonssonAlgebra

/-- An `L`-structure `M` is a *Jónsson algebra* if `L` has countably many function symbols and no
relation symbols, and `M` has no proper substructure of the same cardinality as `M`. -/
def IsJonssonAlgebra (L : FirstOrder.Language) (M : Type*) [L.Structure M] : Prop :=
  L.IsAlgebraic ∧ Countable (Σ n, L.Functions n) ∧
    ∀ S : L.Substructure M, #S = #M → S = ⊤

/-- Does there exist a Jónsson algebra on $\aleph_\omega$? That is, is there a set of cardinality
$\aleph_\omega$ equipped with countably many finitary operations that has no proper subalgebra
of cardinality $\aleph_\omega$?

Equivalently, is $\aleph_\omega$ not a Jónsson cardinal? In ZFC each $\aleph_n$ (for finite $n$)
is known not to be Jónsson, but the question is open for $\aleph_\omega$. -/
@[category research open, AMS 3]
theorem jonsson_algebra :
    answer(sorry) ↔ ∃ (L : FirstOrder.Language.{0, 0}) (M : Type) (_ : L.Structure M),
      #M = ℵ_ ω ∧ IsJonssonAlgebra L M := by
  sorry

/-- The ring `ℤ`, viewed as a structure for the language of rings, is a Jónsson algebra: every
substructure contains `1` and is closed under addition and negation, so it is all of `ℤ`.
In particular there is a Jónsson algebra on $\aleph_0$. -/
@[category test, AMS 3]
theorem isJonssonAlgebra_int :
    letI := Ring.compatibleRingOfRing ℤ
    IsJonssonAlgebra Language.ring ℤ := by
  letI := Ring.compatibleRingOfRing ℤ
  refine ⟨inferInstance, inferInstance, fun S _ => ?_⟩
  have h1 : (1 : ℤ) ∈ S := by
    simpa using S.fun_mem Ring.oneFunc default finZeroElim
  have hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S := fun a ha b hb => by
    simpa using S.fun_mem Ring.addFunc ![a, b] (fun i => by fin_cases i <;> simpa)
  have hneg : ∀ a ∈ S, -a ∈ S := fun a ha => by
    simpa using S.fun_mem Ring.negFunc ![a] (fun i => by fin_cases i; simpa)
  rw [eq_top_iff]
  rintro n -
  induction n using Int.induction_on with
  | zero => simpa using hadd 1 h1 (-1) (hneg 1 h1)
  | succ n hn => exact hadd n hn 1 h1
  | pred n hn => simpa [sub_eq_add_neg] using hadd _ hn (-1) (hneg 1 h1)

/-- An infinite structure for the empty language is not a Jónsson algebra: removing one point
gives a proper substructure of the same cardinality. -/
@[category test, AMS 3]
theorem not_isJonssonAlgebra_empty (M : Type*) [Infinite M] [Language.empty.Structure M] :
    ¬ IsJonssonAlgebra Language.empty M := by
  rintro ⟨-, -, h⟩
  obtain ⟨x⟩ : Nonempty M := inferInstance
  let S : Language.empty.Substructure M := ⟨{x}ᶜ, fun f => Empty.elim f⟩
  have hS : S = ⊤ := h S <| by
    change #({x}ᶜ : Set M) = #M
    exact mk_compl_of_infinite _ <| by simpa using one_lt_aleph0.trans_le (aleph0_le_mk M)
  have hx : x ∈ S := hS ▸ Substructure.mem_top x
  exact hx rfl

end JonssonAlgebra
