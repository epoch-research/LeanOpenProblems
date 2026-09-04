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
# The stable forking conjecture for simple theories

Let $T$ be a complete first-order theory. A formula $\psi(x, y)$ (possibly with parameters) is
*stable* if there are no sequences $(a_i)_{i < \omega}$, $(b_j)_{j < \omega}$ (in a model of $T$)
with $\psi(a_i, b_j)$ if and only if $i \le j$. The theory $T$ is *simple* if no formula
$\varphi(x, y)$ has the tree property.

An instance of forking $a \not\perp_A b$ (i.e. $\operatorname{tp}(a / Ab)$ forks over $A$) is
*stable* if it is witnessed by a stable formula: there is a stable formula $\psi(x, y) \in L(A)$
such that $\psi(a, b)$ holds and $\psi(x, b)$ forks over $A$. The theory $T$ *satisfies stable
forking* if every instance of forking is stable.

The **stable forking conjecture** (Kim–Pillay) states that every simple theory satisfies stable
forking. We formalize the version given in Peretz's paper (Definition, item 4 and the sentence
following it): the witnessing formula may have parameters from the base set $A$.

Forking, dividing, indiscernibility and stability are usually defined inside a monster model.
Here they are defined inside an arbitrary model `M` of `T`, with the relevant sequences and
parameters taken in an elementary extension of `M`; by compactness this is equivalent.
Since every complete simple theory `T` is quantified over, and the conjecture applies in
particular to (a single-sorted coding of) `T^{eq}`, the restriction to real tuples is harmless.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Stable theory](https://en.wikipedia.org/wiki/Stable_theory)
- A. Peretz, *Geometry of forking in simple theories*, [arXiv:math/0412356](https://arxiv.org/abs/math/0412356)
- B. Kim, A. Pillay, *Around stable forking*, Fund. Math. 170 (2001), 107–118
-/

namespace StableForkingConjectureForSimpleTheories

open FirstOrder FirstOrder.Language

universe u v w

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

/-- The formula `ψ(x, y, c)`, with parameters `c` from `M`, is *stable* if there are no
sequences `(aᵢ)`, `(bⱼ)` in an elementary extension `N` of `M` such that `ψ(aᵢ, bⱼ, c)` holds
if and only if `i ≤ j`. -/
def IsStableFormula {n m k : ℕ} (ψ : L.Formula (Fin n ⊕ Fin m ⊕ Fin k)) (c : Fin k → M) : Prop :=
  ¬ ∃ (N : Type (max u v w)) (_ : L.Structure N) (f : M ↪ₑ[L] N)
    (a : ℕ → Fin n → N) (b : ℕ → Fin m → N),
    ∀ i j, ψ.Realize (Sum.elim (a i) (Sum.elim (b j) (f ∘ c))) ↔ i ≤ j

/-- The formula `φ(x, y)` has the *tree property* with respect to the theory `T` if there are
`k` and a tree `(b_η)_{η ∈ ω^{<ω}}` of parameter tuples in some model of `T` such that
for every node `η` the family `{φ(x, b_{η⌢i}) : i < ω}` is `k`-inconsistent, and for every
branch `σ ∈ ω^ω` the set `{φ(x, b_{σ|j}) : j < ω}` is consistent (finitely satisfiable). -/
def HasTreeProperty (T : L.Theory) {n m : ℕ} (φ : L.Formula (Fin n ⊕ Fin m)) : Prop :=
  ∃ (N : Theory.ModelType.{u, v, max u v} T) (k : ℕ) (b : List ℕ → Fin m → N),
    (∀ (η : List ℕ) (s : Finset ℕ), s.card = k →
      ¬ ∃ x : Fin n → N, ∀ i ∈ s, φ.Realize (Sum.elim x (b (η ++ [i])))) ∧
    ∀ (σ : ℕ → ℕ) (l : ℕ), ∃ x : Fin n → N, ∀ j < l, φ.Realize (Sum.elim x (b ((List.range j).map σ)))

/-- A theory `T` is *simple* if no formula `φ(x, y)` has the tree property. -/
def IsSimple (T : L.Theory) : Prop :=
  ∀ (n m : ℕ) (φ : L.Formula (Fin n ⊕ Fin m)), ¬ HasTreeProperty T φ

variable (L) in
/-- A sequence `(dᵢ)_{i < ω}` of tuples in `M` is *indiscernible over* a set `B ⊆ M` if for
every formula `θ(y₀, …, y_{l-1}, z)` and every tuple `c` of parameters from `B`, the truth value
of `θ(d_{i₀}, …, d_{i_{l-1}}, c)` is the same for all increasing index tuples `i₀ < ⋯ < i_{l-1}`.
-/
def IsIndiscernibleOver {β : Type*} (B : Set M) (d : ℕ → β → M) : Prop :=
  ∀ (l k : ℕ) (θ : L.Formula (Fin l × β ⊕ Fin k)) (c : Fin k → M), (∀ i, c i ∈ B) →
    ∀ (i j : Fin l → ℕ), StrictMono i → StrictMono j →
      (θ.Realize (Sum.elim (fun p => d (i p.1) p.2) c) ↔
        θ.Realize (Sum.elim (fun p => d (j p.1) p.2) c))

/-- The formula `φ(x, d)`, with parameters `d` from `M`, *divides over* a set `A ⊆ M` if in some
elementary extension `N` of `M` there is a sequence `(dᵢ)_{i < ω}` indiscernible over `A` with
`d₀ = d` such that `{φ(x, dᵢ) : i < ω}` is `k`-inconsistent for some `k`. -/
def Divides {n : ℕ} {β : Type*} (φ : L.Formula (Fin n ⊕ β)) (d : β → M) (A : Set M) : Prop :=
  ∃ (N : Type (max u v w)) (_ : L.Structure N) (f : M ↪ₑ[L] N) (d' : ℕ → β → N) (k : ℕ),
    d' 0 = f ∘ d ∧ IsIndiscernibleOver L (f '' A) d' ∧
    ∀ s : Finset ℕ, s.card = k → ¬ ∃ x : Fin n → N, ∀ i ∈ s, φ.Realize (Sum.elim x (d' i))

/-- The formula `φ(x, d)`, with parameters `d` from `M`, *forks over* a set `A ⊆ M` if it implies
a finite disjunction `⋁ᵢ ψᵢ(x, eᵢ)` of formulas, each of which divides over `A`. The parameters
`eᵢ` may lie in an elementary extension `N` of `M`. -/
def Forks {n : ℕ} {β : Type*} (φ : L.Formula (Fin n ⊕ β)) (d : β → M) (A : Set M) : Prop :=
  ∃ (N : Type (max u v w)) (_ : L.Structure N) (f : M ↪ₑ[L] N) (l : ℕ) (m : Fin l → ℕ)
    (ψ : ∀ i, L.Formula (Fin n ⊕ Fin (m i))) (e : ∀ i, Fin (m i) → N),
    (∀ i, Divides (ψ i) (e i) (f '' A)) ∧
    ∀ x : Fin n → N, φ.Realize (Sum.elim x (f ∘ d)) → ∃ i, (ψ i).Realize (Sum.elim x (e i))

variable (L) in
/-- The tuple `a` is *independent from* the tuple `b` *over* the set `A ⊆ M`, written
`a ⫝_A b`, if the type `tp(a / A b)` does not fork over `A`: no formula `φ(x, b, c)` with
`c` from `A` that is satisfied by `a` forks over `A`. -/
def IsIndependent {n m : ℕ} (A : Set M) (a : Fin n → M) (b : Fin m → M) : Prop :=
  ¬ ∃ (k : ℕ) (φ : L.Formula (Fin n ⊕ Fin m ⊕ Fin k)) (c : Fin k → M),
    (∀ i, c i ∈ A) ∧ φ.Realize (Sum.elim a (Sum.elim b c)) ∧ Forks φ (Sum.elim b c) A

/-- **The stable forking conjecture for simple theories** (Kim–Pillay; in the form of Peretz,
arXiv:math/0412356, Definition item 4): every complete simple theory `T` satisfies stable forking.
That is, for every model `M` of `T`, every set `A ⊆ M` and all tuples `a`, `b` in `M` with
`a ⫝̸_A b`, there is a stable formula `ψ(x, y) ∈ L(A)` (i.e. `ψ(x, y, c)` with `c` from `A`)
such that `ψ(a, b)` holds and `ψ(x, b)` forks over `A`. -/
theorem stable_forking_conjecture_for_simple_theories {T : L.Theory} (hT : T.IsComplete)
    (hsimple : IsSimple T) [M ⊨ T] (A : Set M) {n m : ℕ} (a : Fin n → M) (b : Fin m → M)
    (hab : ¬ IsIndependent L A a b) :
    ∃ (k : ℕ) (ψ : L.Formula (Fin n ⊕ Fin m ⊕ Fin k)) (c : Fin k → M),
      (∀ i, c i ∈ A) ∧ IsStableFormula ψ c ∧ ψ.Realize (Sum.elim a (Sum.elim b c)) ∧
      Forks ψ (Sum.elim b c) A := by
  sorry

end StableForkingConjectureForSimpleTheories

theorem StableForkingConjectureForSimpleTheories.stable_forking_conjecture_for_simple_theories.disproof : ¬ (type_of% @StableForkingConjectureForSimpleTheories.stable_forking_conjecture_for_simple_theories) := sorry
