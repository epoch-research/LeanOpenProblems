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
# Finite lattice representation problem

The finite lattice representation problem (also called the finite congruence lattice problem)
asks whether every finite lattice is isomorphic to the congruence lattice of some finite algebra.

An *algebra* $\mathbf{A} = \langle A, F \rangle$ is a nonempty set $A$ together with a family
$F$ of finitary operations on $A$. We model it as a `FirstOrder.Language.Structure` on `A` for
a language with no relation symbols. A *congruence* of $\mathbf{A}$ is an equivalence relation
on $A$ that is compatible with every operation in $F$. The congruences of $\mathbf{A}$, ordered
by inclusion, form the *congruence lattice* $\operatorname{Con}(\mathbf{A})$.

The algebra is *finite* when its universe $A$ is finite; no restriction is placed on the number
of operations.

*References:*
- [Wikipedia, Finite lattice representation problem](https://en.wikipedia.org/wiki/Finite_lattice_representation_problem)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [W. DeMeo, *Congruence lattices of finite algebras*, PhD thesis (2012)](https://arxiv.org/abs/1204.4305)
-/

namespace FiniteLatticeRepresentationProblem

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

variable (σ : FirstOrder.Language) (A : Type*) [σ.Structure A]

/-- An equivalence relation `s` on a `σ`-structure `A` is a *congruence* of `A` if it is
compatible with the interpretation of every function symbol `f` of `σ`: whenever
`x i ≈ y i` for all `i`, also `f x ≈ f y`. -/
def IsCongruence (s : Setoid A) : Prop :=
  ∀ {n : ℕ} (f : σ.Functions n) (x y : Fin n → A),
    (∀ i, s (x i) (y i)) → s (funMap f x) (funMap f y)

/-- The *congruence lattice* of a `σ`-structure `A`: the congruences of `A`, ordered by
inclusion, i.e. as a subposet of the complete lattice `Setoid A` of all equivalence relations
on `A`. -/
def CongruenceLattice : Type _ :=
  {s : Setoid A // IsCongruence σ A s}

namespace CongruenceLattice

instance : PartialOrder (CongruenceLattice σ A) :=
  Subtype.partialOrder _

instance : InfSet (CongruenceLattice σ A) where
  sInf S :=
    ⟨sInf (Subtype.val '' S), fun f x y hxy _ ⟨s, hs, hsr⟩ =>
      hsr ▸ s.2 f x y fun i => hxy i s.1 ⟨s, hs, rfl⟩⟩

/-- The congruences of `A` form a complete lattice: they are closed under arbitrary
intersections in `Setoid A`. -/
instance : CompleteLattice (CongruenceLattice σ A) :=
  completeLatticeOfInf _ fun _ =>
    ⟨fun s hs _ _ hxy => hxy s.1 ⟨s, hs, rfl⟩,
      fun _ hs _ _ hxy _ ⟨_, ht, htr⟩ => htr ▸ hs ht hxy⟩

end CongruenceLattice

/-- **Finite lattice representation problem.**
Is every finite lattice isomorphic to the congruence lattice of some finite algebra?

That is, for every finite lattice $L$, is there a finite nonempty set $A$ and a family of
finitary operations on $A$ (a `FirstOrder.Language.Structure` on `A` for a language `σ`
without relation symbols; the family may be infinite) such that $L$ is isomorphic, as a lattice
(equivalently, as a partial order), to the lattice $\operatorname{Con}(\langle A, F \rangle)$
of congruences of this algebra ordered by inclusion?

Lattices are nonempty by convention. Mathlib's `Lattice L` alone allows `L` to be empty, and
the empty type is not a congruence lattice (every congruence lattice contains the equality
relation), so `Nonempty L` is required to exclude this degenerate case. -/
theorem finite_lattice_representation_problem :
    
      ∀ (L : Type*) [Lattice L] [Finite L] [Nonempty L],
        ∃ (A : Type) (σ : FirstOrder.Language.{0, 0}) (_ : σ.Structure A),
          Finite A ∧ Nonempty A ∧ σ.IsAlgebraic ∧
            Nonempty (L ≃o CongruenceLattice σ A) := by
  sorry

end FiniteLatticeRepresentationProblem

theorem FiniteLatticeRepresentationProblem.finite_lattice_representation_problem.disproof : ¬ (type_of% @FiniteLatticeRepresentationProblem.finite_lattice_representation_problem) := sorry
