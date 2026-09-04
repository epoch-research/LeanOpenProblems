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
# Minimal fields of characteristic zero (Podewski's conjecture)

Is every infinite, minimal field of characteristic zero algebraically closed?
Here a structure is *minimal* if every subset of it that is definable
(in one free variable, with parameters) is finite or cofinite.

*References:*
- [Wikipedia, Algebraically closed field](https://en.wikipedia.org/wiki/algebraically_closed_field)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Strongly minimal theory](https://en.wikipedia.org/wiki/Strongly_minimal_theory)
- [F. O. Wagner, *Minimal fields*, J. Symbolic Logic 65 (2000)](https://doi.org/10.2307/2586706)
-/

namespace AlgebraicallyClosed

open FirstOrder FirstOrder.Language FirstOrder.Ring

/-- An `L`-structure `M` is *minimal* if every subset of `M` (in one free variable) that is
definable in the language `L` with parameters from `M` is finite or cofinite. -/
def IsMinimal (L : Language) (M : Type*) [L.Structure M] : Prop :=
  ∀ s : Set M, (Set.univ : Set M).Definable₁ L s → s.Finite ∨ sᶜ.Finite

/--
**Podewski's conjecture.** Is every infinite, minimal field of characteristic zero algebraically
closed?

Here a field $K$ is *minimal* if every subset of $K$ that is definable (in one free variable,
with parameters from $K$) in the first-order language of rings $\{+, \cdot, -, 0, 1\}$ is finite
or cofinite. The hypothesis `CompatibleRing K` says that the `Language.ring`-structure on `K` used
to interpret formulas is the one given by the field operations of `K`. The hypothesis `Infinite K`
is part of the source statement; it is automatic for a field of characteristic zero.

The analogous statement for fields of positive characteristic was proved by Wagner (2000).
-/
theorem algebraically_closed :
    
      ∀ (K : Type*) [Field K] [CharZero K] [Infinite K] [CompatibleRing K],
        IsMinimal Language.ring K → IsAlgClosed K := by
  sorry

end AlgebraicallyClosed

theorem AlgebraicallyClosed.algebraically_closed.disproof : ¬ (type_of% @AlgebraicallyClosed.algebraically_closed) := sorry
