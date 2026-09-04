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
# Cherlin–Zilber conjecture

The Cherlin–Zilber conjecture (also called the algebraicity conjecture) states that an infinite
simple group whose first-order theory is stable in $\aleph_0$ (i.e. $\omega$-stable) is a simple
algebraic group over an algebraically closed field.

Mathlib has neither $\omega$-stability nor algebraic groups, so this file defines both.

* `groupLanguage` is the first-order language of groups $(\cdot, {}^{-1}, 1)$; every group is a
  structure for it.
* A theory `T` is $\omega$-stable (`IsOmegaStable`) if for every model `M` of `T` and every
  countable set `A ⊆ M` of parameters there are only countably many complete types over `A`.
* Algebraic groups over an algebraically closed field `K` are modelled classically as Zariski
  closed subgroups of `GL n K`. This loses no generality: a simple algebraic group is
  noncommutative, hence affine by Chevalley's structure theorem, hence isomorphic to a closed
  subgroup of some `GL n K`. A *simple algebraic group* is a connected noncommutative closed
  subgroup whose only connected closed normal subgroups are the trivial group and itself.

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Model_theory_and_formal_languages)
- [Wikipedia, Stable group](https://en.wikipedia.org/wiki/Stable_group)
- [Wikipedia, Simple algebraic group](https://en.wikipedia.org/wiki/Simple_algebraic_group)
- G. Cherlin, *Groups of small Morley rank*, Ann. Math. Logic 17 (1979), 1–28.
- B. I. Zil'ber, *Groups and rings whose theory is categorical*, Fundam. Math. 95 (1977),
  173–188.
-/

namespace CherlinZilberConjecture

open FirstOrder FirstOrder.Language

universe u v

/- ### $\omega$-stability -/

/--
A first-order theory `T` is *$\omega$-stable* (or *$\aleph_0$-stable*, "stable in $\aleph_0$") if
for every model `M` of `T`, every countable set `A` of parameters from `M` and every `n`, the
space $S_n^M(A)$ of complete `n`-types over `A` is countable.

Here $S_n^M(A)$ is realised as the space of complete types in `n` variables of the complete theory
of `M` in the language `L[[A]]` obtained by adding a constant symbol for each element of `A`.
As for `FirstOrder.Language.Theory.IsSatisfiable`, models are taken in the universe `max u v`; by
the downward Löwenheim–Skolem theorem this is equivalent to allowing models in any universe.
-/
def IsOmegaStable {L : FirstOrder.Language.{u, v}} (T : L.Theory) : Prop :=
  ∀ (M : Theory.ModelType.{u, v, max u v} T) (A : Set M), A.Countable →
    ∀ n : ℕ, Countable ((L[[A]].completeTheory M).CompleteType (Fin n))

/- ### The first-order language of groups -/

/-- The function symbols of the first-order language of groups: `1`, `⁻¹` and `*`. -/
inductive GroupFunc : ℕ → Type
  | one : GroupFunc 0
  | inv : GroupFunc 1
  | mul : GroupFunc 2

/-- The first-order language of groups: the function symbols `1`, `⁻¹`, `*` and no relation
symbols. -/
def groupLanguage : FirstOrder.Language where
  Functions := GroupFunc
  Relations _ := Empty

/-- The constant symbol `1` of the language of groups. -/
abbrev oneFunc : groupLanguage.Functions 0 := GroupFunc.one

/-- The unary function symbol `⁻¹` of the language of groups. -/
abbrev invFunc : groupLanguage.Functions 1 := GroupFunc.inv

/-- The binary function symbol `*` of the language of groups. -/
abbrev mulFunc : groupLanguage.Functions 2 := GroupFunc.mul

/-- Every group is a structure for the language of groups, interpreting the symbols by the group
operations. -/
instance (G : Type*) [Group G] : groupLanguage.Structure G where
  funMap {n} f x :=
    match n, f with
    | _, GroupFunc.one => 1
    | _, GroupFunc.inv => (x 0)⁻¹
    | _, GroupFunc.mul => x 0 * x 1
  RelMap {_} r _ := (r : Empty).elim

section GroupStructure

variable {G : Type*} [Group G]

end GroupStructure

/- ### Simple algebraic groups -/

section AlgebraicGroup

variable {K : Type*} [Field K] {n : ℕ}

/-- A set of `n × n` matrices over `K` is *Zariski closed* if it is the common zero set of a family
of polynomials in the `n²` matrix entries. -/
def IsZariskiClosed (S : Set (Matrix (Fin n) (Fin n) K)) : Prop :=
  ∃ P : Set (MvPolynomial (Fin n × Fin n) K),
    S = {A | ∀ p ∈ P, MvPolynomial.eval (fun ij ↦ A ij.1 ij.2) p = 0}

/-- The Zariski topology on `n × n` matrices over `K`: the topology whose closed sets are the
Zariski closed sets. (The Zariski closed sets are stable under finite unions and arbitrary
intersections, so generating a topology from their complements gives exactly this topology.) -/
def zariskiTopology : TopologicalSpace (Matrix (Fin n) (Fin n) K) :=
  TopologicalSpace.generateFrom {U | IsZariskiClosed Uᶜ}

/-- The set of matrices underlying a subgroup `H` of `GL_n(K)`. -/
def matrixSet (H : Subgroup (GL (Fin n) K)) : Set (Matrix (Fin n) (Fin n) K) :=
  ((↑) : GL (Fin n) K → Matrix (Fin n) (Fin n) K) '' H

/-- A subgroup `H` of `GL_n(K)` is a *linear algebraic group* if it is Zariski closed in
`GL_n(K)`, i.e. it consists of the invertible matrices lying in some Zariski closed set of
matrices. -/
def IsAlgebraicSubgroup (H : Subgroup (GL (Fin n) K)) : Prop :=
  ∃ Z : Set (Matrix (Fin n) (Fin n) K), IsZariskiClosed Z ∧
    ∀ g : GL (Fin n) K, g ∈ H ↔ (g : Matrix (Fin n) (Fin n) K) ∈ Z

/-- A subgroup `H` of `GL_n(K)` is *connected* if it is connected as a subspace of `GL_n(K)` for
the Zariski topology. -/
def IsZariskiConnected (H : Subgroup (GL (Fin n) K)) : Prop :=
  letI := zariskiTopology (K := K) (n := n)
  IsConnected (matrixSet H)

/-- A subgroup `H` of `GL_n(K)` is a *simple algebraic group* if it is a connected noncommutative
linear algebraic group whose only connected closed normal subgroups are the trivial group and `H`
itself. -/
def IsSimpleAlgebraicGroup (H : Subgroup (GL (Fin n) K)) : Prop :=
  IsAlgebraicSubgroup H ∧ IsZariskiConnected H ∧
    (¬ ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) ∧
    ∀ N : Subgroup (GL (Fin n) K), N ≤ H → IsAlgebraicSubgroup N → IsZariskiConnected N →
      (∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N) → N = ⊥ ∨ N = H

end AlgebraicGroup

/--
**The Cherlin–Zilber conjecture** (algebraicity conjecture). Let $G$ be an infinite simple group
whose complete first-order theory (in the language of groups) is stable in $\aleph_0$, i.e.
$\omega$-stable. Then $G$ is a simple algebraic group over an algebraically closed field: there
are an algebraically closed field $K$ and a simple algebraic group $H \le \mathrm{GL}_n(K)$ over
$K$ such that $G \cong H$ as abstract groups.

The hypothesis that $G$ is infinite excludes the finite simple groups, whose theories are
trivially $\omega$-stable. An infinite simple group is automatically nonabelian. Since $G$ is
abstractly simple, any Zariski closed $H \le \mathrm{GL}_n(K)$ with $H \cong G$ is automatically
connected, noncommutative and simple in every usual convention for simple algebraic groups.
-/
theorem cherlin_zilber_conjecture (G : Type u) [Group G] [Infinite G] [IsSimpleGroup G]
    (hG : IsOmegaStable (groupLanguage.completeTheory G)) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (n : ℕ) (H : Subgroup (GL (Fin n) K)),
      IsSimpleAlgebraicGroup H ∧ Nonempty (G ≃* H) := by
  sorry

end CherlinZilberConjecture

theorem CherlinZilberConjecture.cherlin_zilber_conjecture.disproof : ¬ (type_of% @CherlinZilberConjecture.cherlin_zilber_conjecture) := sorry
