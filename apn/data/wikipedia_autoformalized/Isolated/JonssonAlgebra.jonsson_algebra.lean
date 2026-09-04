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
theorem jonsson_algebra :
    ∃ (L : FirstOrder.Language.{0, 0}) (M : Type) (_ : L.Structure M),
      #M = ℵ_ ω ∧ IsJonssonAlgebra L M := by
  sorry

end JonssonAlgebra

theorem JonssonAlgebra.jonsson_algebra.disproof : ¬ (type_of% @JonssonAlgebra.jonsson_algebra) := sorry
