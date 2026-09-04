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
# Decidability of the theory of $\mathbb{F}_p((t))$

Wikipedia's list of unsolved problems in mathematics asks whether the first-order theory of the
field of formal Laurent series over $\mathbb{Z}_p$ is decidable. Here $\mathbb{Z}_p$ is the prime
field $\mathbb{F}_p = \mathbb{Z}/p\mathbb{Z}$: Laurent series over the $p$-adic integers do not
form a field.

The theory of a field $K$ is its complete theory $\mathrm{Th}(K)$ in the first-order language of
rings $\{+, \cdot, -, 0, 1\}$, that is, the set of all sentences true in $K$. It is *decidable* if
there is an algorithm which, given a sentence, decides whether it lies in $\mathrm{Th}(K)$.
Mathlib has no computability structure on first-order sentences, so this file fixes a Gödel
numbering of sentences (`Decidable.godelNumber`, built from
`FirstOrder.Language.BoundedFormula.listEncode`) and defines a theory to be decidable
(`Decidable.IsDecidableTheory`) if some computable function `ℕ → Bool` decides membership on
Gödel numbers.

The existential theory of $\mathbb{F}_p((t))$ in the language of rings is decidable
(Anscombe–Fehm), but the decidability of the full first-order theory is open.

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Decidability (logic)](https://en.wikipedia.org/wiki/Decidability_%28logic%29)
- [S. Anscombe, A. Fehm, *The existential theory of equicharacteristic henselian valued fields*,
  Algebra & Number Theory 10 (2016), 665–683](https://doi.org/10.2140/ant.2016.10.665)
-/

open FirstOrder FirstOrder.Language

namespace Decidable

/-- The five function symbols `+`, `*`, `-`, `0`, `1` of the language of rings, enumerated by
`Fin 5`. -/
def ringFunctionsEquivFin : (Σ i, Language.ring.Functions i) ≃ Fin 5 where
  toFun
    | ⟨_, .add⟩ => 0
    | ⟨_, .mul⟩ => 1
    | ⟨_, .neg⟩ => 2
    | ⟨_, .zero⟩ => 3
    | ⟨_, .one⟩ => 4
  invFun := ![⟨2, .add⟩, ⟨2, .mul⟩, ⟨1, .neg⟩, ⟨0, .zero⟩, ⟨0, .one⟩]
  left_inv := by rintro ⟨_, f⟩; cases f <;> rfl
  right_inv := by decide

/-- An explicit encoding of the function symbols of the language of rings by natural numbers.
It is used to Gödel number the sentences of the language of rings. -/
def ringFunctionsEncodable : Encodable (Σ i, Language.ring.Functions i) :=
  .ofEquiv _ ringFunctionsEquivFin

attribute [local instance] ringFunctionsEncodable

variable {L : Language} [Encodable (Σ i, L.Functions i)] [Encodable (Σ i, L.Relations i)]

/-- The Gödel number of an `L`-sentence `φ`: the natural number encoding the list `φ.listEncode`
of symbols of `φ` (see `FirstOrder.Language.BoundedFormula.listEncode`). -/
def godelNumber (φ : L.Sentence) : ℕ :=
  Encodable.encode φ.listEncode

/-- An `L`-theory `T` (a set of `L`-sentences) is *decidable* if there is a computable function
`f : ℕ → Bool` which, applied to the Gödel number of any sentence `φ`, returns `true` if and
only if `φ ∈ T`. -/
def IsDecidableTheory (T : L.Theory) : Prop :=
  ∃ f : ℕ → Bool, Computable f ∧ ∀ φ : L.Sentence, f (godelNumber φ) = true ↔ φ ∈ T

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/--
Is the first-order theory of the field $\mathbb{F}_p((t))$ of formal Laurent series over the prime
field $\mathbb{F}_p = \mathbb{Z}/p\mathbb{Z}$ decidable? That is, is there an algorithm which,
given a sentence $\varphi$ in the language of rings $\{+, \cdot, -, 0, 1\}$, decides whether
$\mathbb{F}_p((t)) \models \varphi$?

The prime $p$ is an implicit parameter of the question. The statement asks whether
$\mathrm{Th}(\mathbb{F}_p((t)))$ is decidable for every prime $p$.
-/
theorem decidable.parts.i :
    ∀ p : ℕ, p.Prime →
      IsDecidableTheory (Language.ring.completeTheory (LaurentSeries (ZMod p))) := by
  sorry

end Decidable

theorem Decidable.decidable.parts.i.disproof : ¬ (type_of% @Decidable.decidable.parts.i) := sorry
