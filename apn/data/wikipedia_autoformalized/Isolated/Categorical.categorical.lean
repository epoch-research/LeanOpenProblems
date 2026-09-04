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
# Categoricity of the class of atomic models

Let $T$ be a complete first-order theory in a countable language. A model $M$ of $T$ is *atomic*
if every finite tuple $\bar a$ of elements of $M$ realizes an isolated (principal) type over $T$:
there is a formula $\varphi(\bar x)$ true of $\bar a$ such that every formula $\psi(\bar x)$ true
of $\bar a$ satisfies $T \models \forall \bar x\,(\varphi(\bar x) \to \psi(\bar x))$.

The class $K$ of atomic models of $T$ is *categorical in $\lambda$* if $K$ has exactly one model
of cardinality $\lambda$ up to isomorphism. Since $K$ is not an elementary class, the
Löwenheim–Skolem theorems do not provide models of every infinite cardinality, so existence of a
model of cardinality $\lambda$ is part of the definition.

Shelah's problem: if the class of atomic models of a complete first-order theory (in a countable
language) is categorical in $\aleph_n$ for every $n < \omega$, is it categorical in every
infinite cardinal? Shelah proved a positive answer under the set-theoretic assumption
$2^{\aleph_n} < 2^{\aleph_{n+1}}$ for all $n < \omega$; the question in ZFC is open.

*References:*
- [Wikipedia, Categorical theory](https://en.wikipedia.org/wiki/Categorical_%28model_theory%29)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- S. Shelah, *Classification theory for nonelementary classes. I. The number of uncountable models
  of $\psi \in L_{\omega_1,\omega}$. Parts A and B*, Israel J. Math. 46 (1983), 212–240 and 241–273.
- J. T. Baldwin, *Categoricity*, University Lecture Series 50, American Mathematical Society (2009).
-/

namespace Categorical

open FirstOrder FirstOrder.Language Cardinal

universe u v w

variable {L : FirstOrder.Language.{u, v}} (T : L.Theory)

/-- A model `M` of `T` is *atomic* if every finite tuple `a` of elements of `M` realizes an
isolated (principal) complete type: there is a formula `φ` with `M ⊨ φ(a)` such that every
formula `ψ` with `M ⊨ ψ(a)` satisfies `T ⊨ ∀ x, (φ(x) → ψ(x))`. -/
def IsAtomicModel (M : Theory.ModelType.{u, v, w} T) : Prop :=
  ∀ (n : ℕ) (a : Fin n → M), ∃ φ : L.Formula (Fin n),
    φ.Realize a ∧ ∀ ψ : L.Formula (Fin n), ψ.Realize a → φ ⟹[T] ψ

/-- The class of atomic models of `T` is *categorical in `κ`* if `T` has an atomic model of
cardinality `κ` and any two atomic models of `T` of cardinality `κ` are isomorphic.
(Existence is part of the definition: the class of atomic models is not an elementary class, so the
Löwenheim–Skolem theorems do not provide models of every infinite cardinality.) -/
def AtomicModelsCategorical (κ : Cardinal.{w}) : Prop :=
  (∃ M : Theory.ModelType.{u, v, w} T, IsAtomicModel T M ∧ #M = κ) ∧
    ∀ M N : Theory.ModelType.{u, v, w} T, IsAtomicModel T M → IsAtomicModel T N →
      #M = κ → #N = κ → Nonempty (M ≃[L] N)

/--
**Shelah's problem on atomic classes.** Let $T$ be a complete first-order theory in a countable
language. If the class of atomic models of $T$ is categorical in $\aleph_n$ for every
$n < \omega$, is it categorical in every infinite cardinal?

Here "categorical in $\lambda$" means that $T$ has an atomic model of cardinality $\lambda$ and
that all atomic models of $T$ of cardinality $\lambda$ are isomorphic. Since the countable atomic
model of $T$ is unique when it exists, this is the same as asking for categoricity in every
uncountable cardinal. Finite cardinals are excluded: a complete theory with an infinite model has
no finite models.

Shelah proved a positive answer under the set-theoretic assumption
$2^{\aleph_n} < 2^{\aleph_{n+1}}$ for all $n < \omega$; the question in ZFC is open.
-/
theorem categorical :
    
      ∀ (L : FirstOrder.Language.{u, v}) (T : L.Theory), Countable L.Symbols → T.IsComplete →
        (∀ n : ℕ, AtomicModelsCategorical T (ℵ_ n : Cardinal.{w})) →
          ∀ κ : Cardinal.{w}, ℵ₀ ≤ κ → AtomicModelsCategorical T κ := by
  sorry

end Categorical

theorem Categorical.categorical.disproof : ¬ (type_of% @Categorical.categorical) := sorry
