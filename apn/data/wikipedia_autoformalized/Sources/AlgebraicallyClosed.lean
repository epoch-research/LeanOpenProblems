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

/-- Every finite structure is minimal. -/
@[category test, AMS 3]
theorem isMinimal_of_finite (L : Language) (M : Type*) [L.Structure M] [Finite M] :
    IsMinimal L M :=
  fun s _ => Or.inl s.toFinite

/-- The field $\mathbb{R}$ is not minimal: the set of non-negative reals is definable
(by the formula $\exists y,\, y \cdot y = x$) but is neither finite nor cofinite. -/
@[category test, AMS 3 12]
theorem not_isMinimal_real :
    letI := compatibleRingOfRing ℝ
    ¬ IsMinimal Language.ring ℝ := by
  letI := compatibleRingOfRing ℝ
  intro h
  have hdef : (Set.univ : Set ℝ).Definable₁ Language.ring (Set.Ici 0) := by
    refine Set.Definable.mono ?_ (Set.empty_subset _)
    rw [Set.empty_definable_iff]
    refine ⟨∃' ((var (Sum.inr 0) * var (Sum.inr 0)) =' var (Sum.inl 0)), ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ici, Formula.Realize, BoundedFormula.realize_ex,
      BoundedFormula.realize_bdEqual, realize_mul, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
    constructor
    · intro hx
      exact ⟨√(x 0), by simpa [Fin.snoc] using Real.mul_self_sqrt hx⟩
    · rintro ⟨a, ha⟩
      rw [← ha]
      exact mul_self_nonneg _
  rcases h _ hdef with hf | hf
  · exact Set.Ici_infinite 0 hf
  · rw [Set.compl_Ici] at hf
    exact Set.Iio_infinite 0 hf

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
@[category research open, AMS 3 12]
theorem algebraically_closed :
    answer(sorry) ↔
      ∀ (K : Type*) [Field K] [CharZero K] [Infinite K] [CompatibleRing K],
        IsMinimal Language.ring K → IsAlgClosed K := by
  sorry

end AlgebraicallyClosed
