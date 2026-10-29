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
# Sumner's universal tournament conjecture (1971)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Sumner%27s_conjecture)
* [HT91] Häggkvist, R. and Thomason, A. (1991). "Trees in tournaments." *Combinatorica* 11,
  pp. 123--130.
* [ES04] El Sahili, A. (2004). "Trees in tournaments." *J. Combin. Theory Ser. B* 92,
  pp. 183--187.
* [KMO11] Kühn, D., Mycroft, R. and Osthus, D. (2011). "A proof of Sumner's universal
  tournament conjecture for large tournaments." *Proc. London Math. Soc.* 102, pp. 731--766.
  [arXiv:1010.4430](https://arxiv.org/abs/1010.4430)
-/

open SimpleGraph Digraph

namespace SumnerUniversalTournamentConjecture

/-- An **oriented tree**: a digraph that is an orientation of a tree. -/
def IsOrientedTree {W : Type*} (D : Digraph W) : Prop :=
  ∃ T : SimpleGraph W, T.IsTree ∧ D.IsOrientation T

/-- The digraph `D` **embeds** in `D'`: there is an injective digraph homomorphism `D →g D'`. -/
def Embeds {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
    (D : Digraph W) (D' : Digraph V) : Prop :=
  ∃ f : D →g D', Function.Injective f

/--
**Sumner's universal tournament conjecture (1971).**

Every tournament on $2n - 2$ vertices contains every oriented tree on $n \ge 2$ vertices as a
subgraph.
-/
theorem sumner_conjecture :
    ∀ (n : ℕ), 2 ≤ n →
      ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
        Fintype.card W = n → IsOrientedTree D →
        ∀ {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
          Fintype.card V = 2 * n - 2 → G.IsTournament → Embeds D G := by
  sorry

end SumnerUniversalTournamentConjecture

theorem SumnerUniversalTournamentConjecture.sumner_conjecture.disproof : ¬ (type_of% @SumnerUniversalTournamentConjecture.sumner_conjecture) := sorry
