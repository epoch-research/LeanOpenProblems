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
# Finitely presented periodic groups

A group is *periodic* (or a *torsion group*) if every element has finite order. No uniform
bound on the orders is assumed. A group is *finitely presented* if it has a presentation
$\langle S \mid R \rangle$ with a finite set of generators $S$ and a finite set of relators $R$.

The general Burnside problem asked whether every finitely generated periodic group is finite.
Golod and Shafarevich answered it negatively in 1964. It is open whether the answer becomes
positive when "finitely generated" is strengthened to "finitely presented".

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Group_theory)
- [Wikipedia, Presentation of a group](https://en.wikipedia.org/wiki/finitely_presented_group)
- [Wikipedia, Burnside problem](https://en.wikipedia.org/wiki/Burnside_problem)
-/

namespace FinitelyPresented

/-- A group `G` is *finitely presented* if it is isomorphic to `PresentedGroup rels` for some
finite type of generators `α` and some finite set of relators `rels : Set (FreeGroup α)`. -/
def IsFinitelyPresented (G : Type*) [Group G] : Prop :=
  ∃ (α : Type) (_ : Finite α) (rels : Set (FreeGroup α)),
    rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G)

/--
Is every finitely presented periodic group finite?

That is, if a group $G$ has a finite presentation $\langle S \mid R \rangle$ and every element
of $G$ has finite order (with no uniform bound on the orders assumed), must $G$ be finite?
-/
theorem finitely_presented :
    ∀ (G : Type*) [Group G], IsFinitelyPresented G → Monoid.IsTorsion G →
      Finite G := by
  sorry

end FinitelyPresented

theorem FinitelyPresented.finitely_presented.disproof : ¬ (type_of% @FinitelyPresented.finitely_presented) := sorry
