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
# Generalized continuum hypothesis and $\aleph_2$-Suslin trees

The *generalized continuum hypothesis* (GCH) states that $2^\kappa = \kappa^+$ for every
infinite cardinal $\kappa$, equivalently $2^{\aleph_\alpha} = \aleph_{\alpha + 1}$ for every
ordinal $\alpha$.

A (set-theoretic) *tree* is a partial order in which the set of strict predecessors of every
element is well-ordered. The *height* of an element is the order type of its set of strict
predecessors, and the *height* of the tree is the least ordinal strictly greater than the
heights of all its elements. For a cardinal $\kappa$, a *$\kappa$-Suslin tree* is a tree of
height $\kappa$ in which every chain and every antichain has cardinality less than $\kappa$.
(Equivalently, it is a tree of cardinality $\kappa$ all of whose chains and antichains have
cardinality less than $\kappa$.)

Wikipedia's list of unsolved problems in mathematics asks whether GCH implies the existence of
an $\aleph_2$-Suslin tree. Gregory showed that GCH together with $\square_{\omega_1}$ implies
the existence of an $\aleph_2$-Suslin tree. Laver and Shelah showed that, relative to a weakly
compact cardinal, CH is consistent with the nonexistence of $\aleph_2$-Suslin trees; in their
model $2^{\aleph_1} > \aleph_2$, so GCH fails. Whether GCH alone implies the existence of an
$\aleph_2$-Suslin tree is open.

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Generalized continuum hypothesis](https://en.wikipedia.org/wiki/generalized_continuum_hypothesis)
- [Wikipedia, Suslin tree](https://en.wikipedia.org/wiki/Suslin_tree)
- [Wikipedia, Tree (set theory)](https://en.wikipedia.org/wiki/Tree_(set_theory))
- T. Jech, *Set Theory*, The Third Millennium Edition, Springer (2003), Chapter 9.
- [J. Gregory, *Higher Souslin trees and the generalized continuum hypothesis*, J. Symbolic
  Logic 41 (1976), 663–671](https://doi.org/10.2307/2272390)
- [R. Laver and S. Shelah, *The $\aleph_2$-Souslin hypothesis*, Trans. Amer. Math. Soc. 264
  (1981), 411–417](https://doi.org/10.1090/S0002-9947-1981-0603771-7)
-/

universe u

namespace GeneralizedContinuumHypothesis2

open Cardinal Ordinal

/-- The *generalized continuum hypothesis* for the cardinals of universe `u`:
$2^\kappa = \kappa^+$ for every infinite cardinal $\kappa$. Here `Order.succ κ` is the
successor cardinal $\kappa^+$. -/
def GeneralizedContinuumHypothesis : Prop :=
  ∀ κ : Cardinal.{u}, ℵ₀ ≤ κ → 2 ^ κ = Order.succ κ

/-- A (set-theoretic) *tree* is a partial order in which the set `Set.Iio x = {y | y < x}` of
strict predecessors of every element `x` is well-ordered by `<`. -/
class IsTree (T : Type*) [PartialOrder T] : Prop where
  isWellOrder_Iio (x : T) : IsWellOrder (Set.Iio x) (· < ·)

attribute [instance] IsTree.isWellOrder_Iio

/-- Every well-order is a tree. -/
instance isTree_of_wellFoundedLT {α : Type*} [LinearOrder α] [WellFoundedLT α] : IsTree α where
  isWellOrder_Iio _ := inferInstance

variable {T : Type u} [PartialOrder T] [IsTree T]

/-- The *height* of an element `x` of a tree is the order type of its set of strict
predecessors. -/
noncomputable def height (x : T) : Ordinal.{u} := Ordinal.type (α := Set.Iio x) (· < ·)

/-- The *height* of a tree `T` is the least ordinal strictly greater than the heights of all
its elements, that is, the supremum of `height x + 1` over all `x : T`. -/
noncomputable def treeHeight (T : Type u) [PartialOrder T] [IsTree T] : Ordinal.{u} :=
  ⨆ x : T, Order.succ (height x)

/-- For a cardinal `κ`, a tree `T` is a *`κ`-Suslin tree* if it has height `κ` (that is,
`treeHeight T` is the initial ordinal `κ.ord` of `κ`) and every chain and every antichain of
`T` has cardinality less than `κ`.

Some authors require every *branch* (maximal chain) rather than every chain to have cardinality
less than `κ`; since every chain is contained in a branch, this is equivalent. -/
structure IsSuslinTree (κ : Cardinal.{u}) (T : Type u) [PartialOrder T] [IsTree T] : Prop where
  treeHeight_eq : treeHeight T = κ.ord
  mk_lt_of_isChain (C : Set T) : IsChain (· ≤ ·) C → #C < κ
  mk_lt_of_isAntichain (A : Set T) : IsAntichain (· ≤ ·) A → #A < κ

/-- Does the generalized continuum hypothesis imply the existence of an $\aleph_2$-Suslin tree?

That is, does $2^\kappa = \kappa^+$ for every infinite cardinal $\kappa$ imply that there is a
tree of height $\omega_2$ in which every chain and every antichain has cardinality less than
$\aleph_2$? -/
theorem generalized_continuum_hypothesis_2 :
    (GeneralizedContinuumHypothesis.{u} →
      ∃ (T : Type u) (_ : PartialOrder T) (_ : IsTree T), IsSuslinTree (ℵ_ 2) T) := by
  sorry

end GeneralizedContinuumHypothesis2

theorem GeneralizedContinuumHypothesis2.generalized_continuum_hypothesis_2.disproof : ¬ (type_of% @GeneralizedContinuumHypothesis2.generalized_continuum_hypothesis_2) := sorry
