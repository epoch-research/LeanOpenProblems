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
# Partition principle

Does the partition principle (PP) imply the axiom of choice (AC)?

The partition principle says: given two sets $A$ and $B$, if a surjection exists from $A$ to $B$,
then an injection exists from $B$ to $A$. It is a consequence of AC. Whether it implies AC over
ZF is an old open problem in set theory: Russell declared PP to be equivalent to AC in 1906, but
this was never proved or refuted.

*References:*
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia: Axiom of choice](https://en.wikipedia.org/wiki/Axiom_of_choice%23Possibly_equivalent_implications_of_AC)
- [Banaschewski, Moore, The dual Cantor-Bernstein theorem and the partition principle](https://doi.org/10.1305/ndjfl/1093635502)

## Formalisation notes

Lean's ambient logic includes the axiom of choice, so an object-level implication `PP → AC`
about Lean's own types would be trivially true. The question is metatheoretic: is `PP → AC` a
theorem of ZF, i.e. does every model of ZF that satisfies PP also satisfy AC? By Gödel's
completeness theorem these two readings are equivalent.

We therefore work with arbitrary first-order structures `M` for the language of set theory (a
single binary relation `∈`). Such a structure is a model of ZF when it satisfies extensionality,
pairing, union, power set, infinity, regularity and the separation and replacement schemas,
where the schemas range over all first-order formulas of the language with parameters from `M`.
Functions, injections and surjections *inside* `M` are coded, as usual, as sets of Kuratowski
ordered pairs $(x, y) = \{\{x\}, \{x, y\}\}$, as in `ZFSet.IsFunc`.

The `test` declarations at the end check that Mathlib's `ZFSet` is a model of ZF in this sense
and satisfies both the partition principle and the axiom of choice as coded here.
-/

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

namespace PartitionPrinciple

/-- The relation symbols of the first-order language of set theory: a single binary relation
`mem` (membership). -/
inductive SetTheoryRel : ℕ → Type
  | mem : SetTheoryRel 2

/-- The first-order language of set theory: no function symbols and one binary relation `∈`. -/
def setTheory : Language := ⟨fun _ => Empty, SetTheoryRel⟩
  deriving IsRelational

/-- The membership symbol of the language of set theory. -/
abbrev memRel : setTheory.Relations 2 := .mem

variable {M : Type*} [setTheory.Structure M]

/-- The interpretation of the membership symbol in a structure `M` for the language of set
theory: `Mem x y` means "`x ∈ y` holds in `M`". -/
def Mem (x y : M) : Prop := RelMap memRel ![x, y]

@[inherit_doc Mem]
scoped infix:50 " ∈ₘ " => Mem

/-- `s` is the singleton `{x}` in `M`. -/
def IsSingleton (s x : M) : Prop := ∀ z, z ∈ₘ s ↔ z = x

/-- `s` is the unordered pair `{x, y}` in `M`. -/
def IsUnorderedPair (s x y : M) : Prop := ∀ z, z ∈ₘ s ↔ z = x ∨ z = y

/-- `p` is the Kuratowski ordered pair `(x, y) = {{x}, {x, y}}` in `M`. -/
def IsOrderedPair (p x y : M) : Prop :=
  ∀ z, z ∈ₘ p ↔ IsSingleton z x ∨ IsUnorderedPair z x y

/-- The ordered pair `(x, y)` is an element of `f` in `M`. When `f` is a function this says
`f x = y`. -/
def MemPair (f x y : M) : Prop := ∃ p, p ∈ₘ f ∧ IsOrderedPair p x y

/-- `f` is a function with domain `A` in `M`: every element of `f` is an ordered pair whose first
coordinate lies in `A`, and every `x ∈ A` has exactly one `y` with `(x, y) ∈ f`. -/
def IsFunction (f A : M) : Prop :=
  (∀ p, p ∈ₘ f → ∃ x y, x ∈ₘ A ∧ IsOrderedPair p x y) ∧
  (∀ x, x ∈ₘ A → ∃ y, MemPair f x y) ∧
  (∀ x y y', MemPair f x y → MemPair f x y' → y = y')

/-- `f` is a function from `A` to `B` in `M`. -/
def IsFunctionOn (f A B : M) : Prop :=
  IsFunction f A ∧ ∀ x y, MemPair f x y → y ∈ₘ B

/-- `f` is a surjection from `A` onto `B` in `M`. -/
def IsSurjectionOn (f A B : M) : Prop :=
  IsFunctionOn f A B ∧ ∀ y, y ∈ₘ B → ∃ x, MemPair f x y

/-- `f` is an injection from `A` into `B` in `M`. -/
def IsInjectionOn (f A B : M) : Prop :=
  IsFunctionOn f A B ∧ ∀ x x' y, MemPair f x y → MemPair f x' y → x = x'

/-- A structure `M` for the language of set theory is a model of ZF: it satisfies extensionality,
pairing, union, power set, infinity, regularity, and the separation and replacement schemas. The
schemas range over all first-order formulas of the language, with arbitrary parameters from
`M`. -/
structure IsZFModel (M : Type*) [setTheory.Structure M] : Prop where
  /-- Extensionality: sets with the same elements are equal. -/
  extensionality : ∀ x y : M, (∀ z, z ∈ₘ x ↔ z ∈ₘ y) → x = y
  /-- Pairing: for all `x`, `y` the unordered pair `{x, y}` exists. -/
  pairing : ∀ x y : M, ∃ p, IsUnorderedPair p x y
  /-- Union: for every `x` the union `⋃ x` exists. -/
  union : ∀ x : M, ∃ u, ∀ z, z ∈ₘ u ↔ ∃ y, y ∈ₘ x ∧ z ∈ₘ y
  /-- Power set: for every `x` the set of all subsets of `x` exists. -/
  powerset : ∀ x : M, ∃ p, ∀ z, z ∈ₘ p ↔ ∀ w, w ∈ₘ z → w ∈ₘ x
  /-- Infinity: there is a set containing `∅` and closed under `x ↦ x ∪ {x}`. -/
  infinity : ∃ I : M, (∃ e, e ∈ₘ I ∧ ∀ z, ¬ z ∈ₘ e) ∧
    ∀ x, x ∈ₘ I → ∃ s, s ∈ₘ I ∧ ∀ z, z ∈ₘ s ↔ z ∈ₘ x ∨ z = x
  /-- Regularity: every nonempty set has an `∈`-minimal element. -/
  regularity : ∀ x : M, (∃ y, y ∈ₘ x) → ∃ y, y ∈ₘ x ∧ ∀ z, z ∈ₘ y → ¬ z ∈ₘ x
  /-- Separation schema: for every formula `φ(z, w₁, …, wₙ)` and parameters `w₁, …, wₙ`, the set
  `{z ∈ x | φ(z, w₁, …, wₙ)}` exists. -/
  separation : ∀ (n : ℕ) (φ : setTheory.BoundedFormula (Fin n) 1) (w : Fin n → M) (x : M),
    ∃ y, ∀ z, z ∈ₘ y ↔ z ∈ₘ x ∧ φ.Realize w ![z]
  /-- Replacement schema: for every formula `φ(a, b, w₁, …, wₙ)` and parameters `w₁, …, wₙ`, if
  `φ` defines a function on `x` then the image of `x` under this function exists. -/
  replacement : ∀ (n : ℕ) (φ : setTheory.BoundedFormula (Fin n) 2) (w : Fin n → M) (x : M),
    (∀ a, a ∈ₘ x → ∃! b, φ.Realize w ![a, b]) →
    ∃ y, ∀ b, b ∈ₘ y ↔ ∃ a, a ∈ₘ x ∧ φ.Realize w ![a, b]

/-- The partition principle holds in `M`: for all sets `A`, `B` in `M`, if there is a surjection
from `A` onto `B` in `M` then there is an injection from `B` into `A` in `M`. -/
def PartitionPrincipleHolds (M : Type*) [setTheory.Structure M] : Prop :=
  ∀ A B : M, (∃ f, IsSurjectionOn f A B) → ∃ g, IsInjectionOn g B A

/-- The axiom of choice holds in `M`: for every set `X` of nonempty sets in `M`, there is a
choice function `f` in `M` with domain `X` such that `f x ∈ x` for every `x ∈ X`. -/
def AxiomOfChoiceHolds (M : Type*) [setTheory.Structure M] : Prop :=
  ∀ X : M, (∀ x, x ∈ₘ X → ∃ z, z ∈ₘ x) →
    ∃ f, IsFunction f X ∧ ∀ x, x ∈ₘ X → ∃ z, z ∈ₘ x ∧ MemPair f x z

/-- **Partition principle problem.** Does the partition principle imply the axiom of choice?

That is, is `PP → AC` a theorem of ZF: does every model of ZF that satisfies the partition
principle (whenever there is a surjection from `A` onto `B`, there is an injection from `B`
into `A`) also satisfy the axiom of choice (every set of nonempty sets has a choice function)?
By Gödel's completeness theorem, this is equivalent to `PP → AC` being provable in ZF. -/
theorem partition_principle :
    ∀ (M : Type*) [setTheory.Structure M],
      IsZFModel M → PartitionPrincipleHolds M → AxiomOfChoiceHolds M := by
  sorry

/- ## Sanity checks

Mathlib's `ZFSet` (the von Neumann universe built inside Lean) is a model of ZF in the above
sense, and it satisfies both the partition principle and the axiom of choice as coded above.
This checks that the definitions are satisfiable and that the coding of functions is sensible.
-/

/-- `ZFSet` as a structure for the language of set theory. -/
instance zfSetStructure : setTheory.Structure ZFSet where
  RelMap | .mem => fun v => v 0 ∈ v 1

end PartitionPrinciple

theorem PartitionPrinciple.partition_principle.disproof : ¬ (type_of% @PartitionPrinciple.partition_principle) := sorry
