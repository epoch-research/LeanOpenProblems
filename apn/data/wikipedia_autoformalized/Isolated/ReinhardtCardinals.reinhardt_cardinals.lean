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
# Reinhardt cardinals

A *Reinhardt cardinal* is the critical point of a nontrivial elementary embedding $j : V \to V$
of the set-theoretic universe into itself. Kunen (1971) showed that no such embedding exists
in $\mathsf{ZFC}$ (or in $\mathsf{NBG}$ with the axiom of choice). Suzuki (1999) showed that in
$\mathsf{ZF}$ no such embedding is definable from parameters. Whether such an embedding can
exist without the axiom of choice is open.

Following the Wikipedia article, the question is made precise as the consistency of the
first-order theory $\mathsf{ZF}_j + $ “$j$ is a nontrivial elementary embedding”: the language of
set theory is extended by a unary function symbol $j$, and the axioms are
* the axioms of $\mathsf{ZF}$, with the Separation and Collection schemas for all formulas of the
  extended language (so classes defined using $j$ are allowed),
* the elementarity scheme $\forall \vec x\,(\varphi(\vec x) \leftrightarrow \varphi(j(\vec x)))$
  for every formula $\varphi$ of the language of set theory (not mentioning $j$),
* nontriviality: $\exists x\, j(x) \neq x$.

By the completeness theorem, this theory is consistent if and only if it has a model, so the
question is stated as the satisfiability of the theory.

The file builds the language `{∈, j}` and the theory explicitly, using Mathlib's first-order
logic (`FirstOrder.Language`). The `API` lemmas at the end unfold each axiom in an arbitrary
structure, to check the variable indices.

*References:*
* [Wikipedia, Reinhardt cardinal](https://en.wikipedia.org/wiki/Reinhardt_cardinal)
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* K. Kunen, *Elementary embeddings and infinitary combinatorics*,
  J. Symbolic Logic 36 (1971), 407–413.
* A. Suzuki, *No elementary embedding from V into V is definable from parameters*,
  J. Symbolic Logic 64 (1999), 1591–1594.
-/

namespace ReinhardtCardinals

open FirstOrder FirstOrder.Language

/-- The relation symbols of the language of set theory: one binary relation `∈`. -/
inductive SetRel : ℕ → Type
  | mem : SetRel 2

/-- The function symbols added to the language of set theory: one unary function `j`. -/
inductive JFunc : ℕ → Type
  | j : JFunc 1

/-- The language of set theory `{∈}`. -/
def setLang : Language := ⟨fun _ => Empty, SetRel⟩

/-- The language of set theory with one extra unary function symbol: `{∈, j}`. -/
def jLang : Language := ⟨JFunc, SetRel⟩

/-- The inclusion of the language `{∈}` into the language `{∈, j}`. -/
def setLangHom : setLang →ᴸ jLang := ⟨fun _ => Empty.elim, fun _ => id⟩

/-- The atomic formula `t₁ ∈ t₂` of the language `{∈, j}`. -/
def memRel {α : Type} {n : ℕ} (t₁ t₂ : jLang.Term (α ⊕ Fin n)) : jLang.BoundedFormula α n :=
  Relations.boundedFormula₂ SetRel.mem t₁ t₂

@[inherit_doc] local infixl:88 " ∈' " => memRel

/-- The term `j(t)` of the language `{∈, j}`. -/
def japp {α : Type} (t : jLang.Term α) : jLang.Term α :=
  Functions.apply₁ JFunc.j t

/-- The universal closure `∀ x₀ … ∀ x_{k-1}, φ` of a formula `φ` with free variables in `Fin k`. -/
def univClosure {k : ℕ} (φ : jLang.Formula (Fin k)) : jLang.Sentence :=
  (BoundedFormula.relabel (Sum.inr : Fin k → Empty ⊕ Fin k) φ).alls

/-
### The axioms of `ZF` in the language `{∈, j}`

Bound variables are written with de Bruijn indices: `&0` is the outermost quantified variable.
-/

/-- Extensionality: `∀ x ∀ y (∀ z (z ∈ x ↔ z ∈ y) → x = y)`. -/
def extensionality : jLang.Sentence :=
  ∀' ∀' ((∀' ((&2 ∈' &0) ⇔ (&2 ∈' &1))) ⟹ (&0 =' &1))

/-- Empty set: `∃ x ∀ y ¬ (y ∈ x)`. -/
def emptySet : jLang.Sentence :=
  ∃' ∀' ∼(&1 ∈' &0)

/-- Pairing: `∀ x ∀ y ∃ p ∀ z (z ∈ p ↔ z = x ∨ z = y)`. -/
def pairing : jLang.Sentence :=
  ∀' ∀' ∃' ∀' ((&3 ∈' &2) ⇔ ((&3 =' &0) ⊔ (&3 =' &1)))

/-- Union: `∀ x ∃ u ∀ z (z ∈ u ↔ ∃ y (y ∈ x ∧ z ∈ y))`. -/
def union : jLang.Sentence :=
  ∀' ∃' ∀' ((&2 ∈' &1) ⇔ ∃' ((&3 ∈' &0) ⊓ (&2 ∈' &3)))

/-- Power set: `∀ x ∃ p ∀ z (z ∈ p ↔ ∀ w (w ∈ z → w ∈ x))`. -/
def powerset : jLang.Sentence :=
  ∀' ∃' ∀' ((&2 ∈' &1) ⇔ ∀' ((&3 ∈' &2) ⟹ (&3 ∈' &0)))

/-- Infinity:
`∃ x (∃ e (e ∈ x ∧ ∀ z ¬ (z ∈ e)) ∧ ∀ y (y ∈ x → ∃ s (s ∈ x ∧ ∀ z (z ∈ s ↔ z ∈ y ∨ z = y))))`,
i.e. there is a set containing the empty set and closed under `y ↦ y ∪ {y}`. -/
def infinity : jLang.Sentence :=
  ∃' ((∃' ((&1 ∈' &0) ⊓ ∀' ∼(&2 ∈' &1))) ⊓
    ∀' ((&1 ∈' &0) ⟹ ∃' ((&2 ∈' &0) ⊓ ∀' ((&3 ∈' &2) ⇔ ((&3 ∈' &1) ⊔ (&3 =' &1))))))

/-- Foundation (regularity): `∀ x (∃ y (y ∈ x) → ∃ y (y ∈ x ∧ ∀ z (z ∈ y → ¬ (z ∈ x))))`. -/
def foundation : jLang.Sentence :=
  ∀' ((∃' (&1 ∈' &0)) ⟹ ∃' ((&1 ∈' &0) ⊓ ∀' ((&2 ∈' &1) ⟹ ∼(&2 ∈' &0))))

/-- The Separation axiom for a formula `φ(w⃗, z, x)` of the language `{∈, j}`, with parameters
`w⃗ : Fin k` (the free variables of `φ`) and two bound variables `z = &0`, `x = &1`:
`∀ w⃗ ∀ z ∃ y ∀ x (x ∈ y ↔ (x ∈ z ∧ φ(w⃗, z, x)))`.
The new variable `y` (`&1` in the axiom) is not free in `φ`; `φ.liftAt 1 1` shifts `x` to `&2`. -/
def separation {k : ℕ} (φ : jLang.BoundedFormula (Fin k) 2) : jLang.Sentence :=
  univClosure <| ∀' ∃' ∀' ((&2 ∈' &1) ⇔ ((&2 ∈' &0) ⊓ φ.liftAt 1 1))

/-- The Collection axiom for a formula `φ(w⃗, x, y)` of the language `{∈, j}`, with parameters
`w⃗ : Fin k` (the free variables of `φ`) and two bound variables `x = &0`, `y = &1`:
`∀ w⃗ ∀ a (∀ x (x ∈ a → ∃ y φ(w⃗, x, y)) → ∃ b ∀ x (x ∈ a → ∃ y (y ∈ b ∧ φ(w⃗, x, y))))`.
The new variables `a` and `b` are not free in `φ`; `φ.liftAt 1 0` and `φ.liftAt 2 0` shift `x, y`
to `&1, &2` and to `&2, &3` respectively. -/
def collection {k : ℕ} (φ : jLang.BoundedFormula (Fin k) 2) : jLang.Sentence :=
  univClosure <| ∀' ((∀' ((&1 ∈' &0) ⟹ ∃' φ.liftAt 1 0)) ⟹
    ∃' ∀' ((&2 ∈' &0) ⟹ ∃' ((&3 ∈' &1) ⊓ φ.liftAt 2 0)))

/-- The theory `ZF_j`: the axioms of `ZF` in the language `{∈, j}`, where the Separation and
Collection schemas range over all formulas of the extended language (including those
mentioning `j`). -/
def zfJ : jLang.Theory :=
  {extensionality, emptySet, pairing, union, powerset, infinity, foundation} ∪
    {σ | ∃ (k : ℕ) (φ : jLang.BoundedFormula (Fin k) 2), σ = separation φ} ∪
    {σ | ∃ (k : ℕ) (φ : jLang.BoundedFormula (Fin k) 2), σ = collection φ}

/-
### `j` is a nontrivial elementary embedding `V → V`
-/

/-- The elementarity axiom for a formula `φ(x₀, …, x_{k-1})` of the language of set theory `{∈}`
(not mentioning `j`): `∀ x⃗ (φ(x⃗) ↔ φ(j(x₀), …, j(x_{k-1})))`. -/
def elementarity {k : ℕ} (φ : setLang.Formula (Fin k)) : jLang.Sentence :=
  univClosure <| (setLangHom.onFormula φ) ⇔
    (setLangHom.onFormula φ).subst fun i => japp (Term.var i)

/-- Nontriviality: `∃ x, j(x) ≠ x`. -/
def nontrivial : jLang.Sentence :=
  ∃' ∼(japp (&0) =' &0)

/-- The theory `ZF_j + "j : V → V is a nontrivial elementary embedding"`: `ZF` with Separation and
Collection for all formulas involving `j`, the elementarity scheme for all formulas of the
language of set theory, and `∃ x, j(x) ≠ x`. A model of this theory is a universe of `ZF`
together with a Reinhardt embedding; its critical point is a Reinhardt cardinal. -/
def reinhardtTheory : jLang.Theory :=
  zfJ ∪ {σ | ∃ (k : ℕ) (φ : setLang.Formula (Fin k)), σ = elementarity φ} ∪ {nontrivial}

/--
**Reinhardt cardinals.** Without assuming the axiom of choice, can a nontrivial elementary
embedding $j : V \to V$ exist? That is, is the theory
$\mathsf{ZF}_j + $ “$j : V \to V$ is a nontrivial elementary embedding” consistent, where
$\mathsf{ZF}_j$ is $\mathsf{ZF}$ in the language with the extra function symbol $j$, with
Separation and Collection for all formulas involving $j$?

By the completeness theorem, consistency of the theory is equivalent to the existence of a
model, so the question is formalized as `reinhardtTheory.IsSatisfiable`. A positive answer
(`answer(True)`) means that such an embedding can consistently exist; a negative answer means
that Reinhardt cardinals are inconsistent with `ZF`.

Here `j` is a primitive function symbol, not a class definable from parameters: Suzuki (1999)
showed that no definable class is such an embedding. The axiom of choice is not assumed: Kunen
(1971) showed that no such embedding exists in `ZFC` (or `NBG` with choice).
-/
theorem reinhardt_cardinals : reinhardtTheory.IsSatisfiable := by
  sorry

/-
### API: the meaning of the axioms in a structure

Each lemma unfolds one axiom in an arbitrary `{∈, j}`-structure `M`.
-/

section API

variable {M : Type} [jLang.Structure M]

/-- The interpretation of `∈` in `M`. -/
local notation:50 x " ∈ₘ " y => Structure.RelMap (L := jLang) SetRel.mem ![x, y]

/-- The interpretation of `j` in `M`. -/
local notation "jₘ" => fun x => Structure.funMap (L := jLang) JFunc.j ![x]

end API

end ReinhardtCardinals

theorem ReinhardtCardinals.reinhardt_cardinals.disproof : ¬ (type_of% @ReinhardtCardinals.reinhardt_cardinals) := sorry
