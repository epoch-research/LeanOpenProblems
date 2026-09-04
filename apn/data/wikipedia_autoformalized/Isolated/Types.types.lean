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
# Types (model theory): models omitting countably many types

A *type* (over the empty set) in the free variables $x_0, \dots, x_{n-1}$ is a set of
first-order formulas whose free variables lie among $x_0, \dots, x_{n-1}$. A structure
$\mathcal{M}$ *omits* the type if no $n$-tuple of elements of $\mathcal{M}$ satisfies every
formula in it.

Assume $K$ is the class of models of a countable first order theory omitting countably many
types. If $K$ has a model of cardinality $\aleph_{\omega_1}$, does it have a model of cardinality
continuum?

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Model_theory_and_formal_languages)
- [Wikipedia, Type (model theory)](https://en.wikipedia.org/wiki/Type_%28model_theory%29)
- [S. Shelah, *Borel sets with large squares*, Fund. Math. 159 (1999), 1–50](https://arxiv.org/abs/math/9802134)
-/

universe u v w

open Cardinal FirstOrder.Language
open scoped Ordinal

namespace Types

variable {L : FirstOrder.Language.{u, v}}

/-- A structure `M` *omits* the (partial) type `p`, a set of `L`-formulas in the free variables
`x_0, …, x_{n-1}`, if no `n`-tuple of elements of `M` satisfies every formula in `p`.
No consistency requirement is imposed on `p`: a set of formulas that is inconsistent with the
ambient theory is omitted by every model of it. -/
def Omits (M : Type*) [L.Structure M] {n : ℕ} (p : Set (L.Formula (Fin n))) : Prop :=
  ¬ ∃ v : Fin n → M, ∀ φ ∈ p, φ.Realize v

/-- The class `K` of models of the theory `T` that omit every type in the family `Γ`.
Each member of `Γ` is a type in some finite number `n` of free variables. -/
def modelsOmitting (T : L.Theory) (Γ : Set (Σ n : ℕ, Set (L.Formula (Fin n)))) :
    Set (Theory.ModelType.{u, v, w} T) :=
  {M | ∀ p ∈ Γ, Omits M p.2}

/--
Assume $K$ is the class of models of a countable first order theory $T$ omitting countably many
types. If $K$ has a model of cardinality $\aleph_{\omega_1}$, does it have a model of cardinality
continuum $2^{\aleph_0}$?

Here a countable first order theory is a theory in a language with countably many symbols, and
a type is any set of formulas (over the empty set) in finitely many free variables, complete
or partial. `answer(True)` means that the answer is "yes" for every such $T$ and family of types.
-/
theorem types :
    ∀ (L : FirstOrder.Language.{u, v}) [Countable L.Symbols] (T : L.Theory)
      (Γ : Set (Σ n : ℕ, Set (L.Formula (Fin n)))), Γ.Countable →
      (∃ M ∈ modelsOmitting.{u, v, w} T Γ, #M = ℵ_ ω₁) →
      ∃ M ∈ modelsOmitting.{u, v, w} T Γ, #M = 𝔠 := by
  sorry

end Types

theorem Types.types.disproof : ¬ (type_of% @Types.types) := sorry
