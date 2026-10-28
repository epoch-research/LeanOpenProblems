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
# Alspach's conjecture on cycle decompositions of complete graphs (1981; proved 2014)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Alspach%27s_conjecture)
* [Al81] Alspach, B. (1981). "Research problems, Problem 3." *Discrete Math.* 36, p. 333.
* [BHP14] Bryant, D., Horsley, D. and Pettersson, W. (2014). "Cycle decompositions V:
  Complete graphs into cycles of arbitrary lengths." *Proc. London Math. Soc.* 108,
  pp. 1153--1192. [arXiv:1204.3709](https://arxiv.org/abs/1204.3709)
* [GJKKO21] Glock, S., Joos, F., Kim, J., Kühn, D. and Osthus, D. (2021). "Resolution of the
  Oberwolfach problem." *J. Eur. Math. Soc.* 23, pp. 2511--2547.
  [arXiv:1806.04644](https://arxiv.org/abs/1806.04644)
-/

open SimpleGraph Finset

namespace AlspachConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- A multiset of cycles `C` is a **cycle decomposition** of `G` if every edge of `G` lies on
exactly one of the cycles. -/
def IsCycleDecomposition (G : SimpleGraph V) [DecidableRel G.Adj] (C : Multiset (Cycle G)) :
    Prop :=
  ∀ e ∈ G.edgeFinset, (C.filter fun c => e ∈ c.edges).card = 1

/-- The multiset of cycle lengths of a family of cycles. -/
def lengths {G : SimpleGraph V} (C : Multiset (Cycle G)) : Multiset ℕ :=
  C.map SimpleGraph.Cycle.length

/-- The triangle `0 → 1 → 2 → 0` as a cycle of `K₃`. -/
def triangle : Cycle (completeGraph (Fin 3)) where
  base := 0
  walk := Walk.cons (by decide : (completeGraph (Fin 3)).Adj 0 1)
    (Walk.cons (by decide : (completeGraph (Fin 3)).Adj 1 2)
      (Walk.cons (by decide : (completeGraph (Fin 3)).Adj 2 0) Walk.nil))
  isCycle := by
    rw [Walk.isCycle_def, Walk.isTrail_def]
    exact ⟨by decide, by simp, by decide⟩

/-- The exceptional Oberwolfach $2$-factor `C₄ + C₅` on nine vertices. -/
def oberwolfachException9 : SimpleGraph (Fin 4 ⊕ Fin 5) :=
  cycleGraph 4 ⊕g cycleGraph 5

/-- The exceptional Oberwolfach $2$-factor `C₃ + C₃ + C₅` on eleven vertices. -/
def oberwolfachException11 : SimpleGraph ((Fin 3 ⊕ Fin 3) ⊕ Fin 5) :=
  (cycleGraph 3 ⊕g cycleGraph 3) ⊕g cycleGraph 5

/--
**The Oberwolfach problem (Ringel 1967).**

For odd $n$ and a $2$-regular graph $F$ on $n$ vertices, can $K_n$ be decomposed into
$(n-1)/2$ spanning subgraphs isomorphic to $F$? The decomposition is known to be impossible for
exactly two pairs with odd $n$ — $(9, C_4 + C_5)$ and $(11, C_3 + C_3 + C_5)$ — and is
conjectured to exist in every other case. Known for all sufficiently large $n$ [GJKKO21].
-/
theorem alspach_conjecture.variants.oberwolfach :
    ∀ (n : ℕ), Odd n → 3 ≤ n →
      ∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj], (∀ v, F.degree v = 2) →
      IsEmpty (F ≃g oberwolfachException9) → IsEmpty (F ≃g oberwolfachException11) →
      ∃ D : Fin ((n - 1) / 2) → SimpleGraph (Fin n),
        (∀ i, Nonempty (D i ≃g F)) ∧
        ∀ u v, (completeGraph (Fin n)).Adj u v ↔ ∃! i, (D i).Adj u v := by
  sorry

end AlspachConjecture

theorem AlspachConjecture.alspach_conjecture.variants.oberwolfach.disproof : ¬ (type_of% @AlspachConjecture.alspach_conjecture.variants.oberwolfach) := sorry
