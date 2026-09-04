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
# Reducts of homogeneous structures (Thomas' conjecture)

"Does a finitely presented homogeneous structure for a finite relational language have finitely
many reducts?"

This is Thomas' conjecture (1991) on the reducts of countably infinite homogeneous structures in a
finite relational language. Here a *reduct* of a structure $M$ is a relational structure $N$ on
the same domain each of whose relations is first-order definable in $M$ without parameters, and
reducts are counted up to first-order interdefinability: two reducts are identified when each is
a reduct of the other, i.e. when they have the same relations definable without parameters.
(Counting reducts in the narrower sense of "forgetting some relation symbols" would make the
question trivial for a finite language.)

*Homogeneous* means ultrahomogeneous: every isomorphism between finite substructures of $M$
extends to an automorphism of $M$. Since such a structure is $\omega$-categorical, the conjecture
is equivalent to asking whether there are only finitely many closed permutation groups $G$ with
$\mathrm{Aut}(M) \le G \le \mathrm{Sym}(M)$.

*References:*
- [Wikipedia: Reduct](https://en.wikipedia.org/wiki/reduct)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- S. Thomas, *Reducts of the random graph*, J. Symbolic Logic 56 (1991), 176–181.
  <https://doi.org/10.2307/2274912>
- M. Bodirsky, M. Pinsker, *Reducts of Ramsey structures*, Contemp. Math. 558 (2011), 489–519.
  <https://arxiv.org/abs/1105.6073>
-/

namespace Reduct

open FirstOrder FirstOrder.Language

universe u v w

variable (L : FirstOrder.Language.{u, v}) (M : Type w) [L.Structure M]

/-- The set of all finitary relations on `M` (recorded together with their arity) that are
first-order definable without parameters in the `L`-structure `M`. -/
def definableRelations : Set (Σ n : ℕ, Set (Fin n → M)) :=
  {R | (∅ : Set M).Definable L R.2}

/-- A structure `N` on the same domain `M` (in a language `L'`) is a *reduct* of the
`L`-structure `M` if every relation of `N` is first-order definable without parameters in `M`. -/
def IsReduct {L' : FirstOrder.Language.{w, w}} (N : L'.Structure M) : Prop :=
  ∀ (n : ℕ) (R : L'.Relations n), (∅ : Set M).Definable L {x | N.RelMap R x}

/-- The reducts of the `L`-structure `M` up to first-order interdefinability. Each reduct `N`
(a structure on `M` in a relational language) is represented by the set of relations definable
without parameters in `N`; two reducts are interdefinable exactly when these sets coincide.

The reduct languages are taken in the universe of `M`. This loses nothing: every reduct is
interdefinable with the reduct whose relation symbols are its own relations, which are sets
of tuples of elements of `M`. -/
def reductClasses : Set (Set (Σ n : ℕ, Set (Fin n → M))) :=
  {D | ∃ (L' : FirstOrder.Language.{w, w}) (_ : L'.IsRelational) (N : L'.Structure M),
    IsReduct L M N ∧ D = @definableRelations L' M N}

/--
**Thomas' conjecture** (1991). "Does a finitely presented homogeneous structure for a finite
relational language have finitely many reducts?"

Precisely: is it true that for every countably infinite structure $M$ in a finite relational
language which is homogeneous (every isomorphism between finite substructures of $M$ extends to
an automorphism of $M$), there are only finitely many reducts of $M$ up to first-order
interdefinability? Here a reduct of $M$ is a structure on the domain of $M$ all of whose relations
are first-order definable without parameters in $M$. The conjectured answer is yes.
-/
theorem reduct : 
    ∀ (L : FirstOrder.Language.{u, v}) (M : Type w) [L.Structure M] [L.IsRelational]
      [Finite L.Symbols] [Countable M] [Infinite M],
      L.IsUltrahomogeneous M → (reductClasses L M).Finite := by
  sorry

end Reduct

theorem Reduct.reduct.disproof : ¬ (type_of% @Reduct.reduct) := sorry
