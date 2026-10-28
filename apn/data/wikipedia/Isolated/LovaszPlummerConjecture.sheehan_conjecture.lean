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
# The Lovász–Plummer conjecture (proved 2011) and Sheehan's conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Petersen%27s_theorem#Related_conjectures)
* [LP86] Lovász, L. and Plummer, M. D. (1986). *Matching Theory.* North-Holland.
* [EKKKN11] Esperet, L., Kardoš, F., King, A. D., Král', D. and Norine, S. (2011).
  "Exponentially many perfect matchings in cubic graphs." *Adv. Math.* 227, pp. 1646--1664.
  [arXiv:1012.2878](https://arxiv.org/abs/1012.2878)
* [Sh77] Sheehan, J. (1977). "The multiplicity of Hamiltonian circuits in a graph." In *Recent
  Advances in Graph Theory*, Academia, Prague, pp. 477--480.
* [Th98] Thomassen, C. (1998). "Independent dominating sets and a second Hamiltonian cycle in
  regular graphs." *J. Combin. Theory Ser. B* 72, pp. 104--109.
-/

open SimpleGraph

namespace LovaszPlummerConjecture

variable {V : Type*}

/-- The number of perfect matchings of `G`. -/
noncomputable def perfectMatchingCount (G : SimpleGraph V) : ℕ :=
  {M : G.Subgraph | M.IsPerfectMatching}.ncard

/-- A **Hamiltonian cycle** of `G`: a cycle passing through every vertex. -/
def IsHamiltonianCycle (G : SimpleGraph V) {v : V} (c : G.Walk v v) : Prop :=
  c.IsCycle ∧ ∀ w, w ∈ c.support

/--
**Sheehan's conjecture (1977).**

Every $4$-regular graph with a Hamiltonian cycle has a second Hamiltonian cycle (one with a
different edge set). Sheehan's conjecture would settle the last open case of the question,
raised by Smith's theorem for cubic graphs, of which regular Hamiltonian graphs have a second
Hamiltonian cycle: Thomassen [Th98] proved it for all $r$-regular graphs with $r \ge 300$.
-/
theorem sheehan_conjecture :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v, G.degree v = 4) →
      ∀ (v : V) (c : G.Walk v v), IsHamiltonianCycle G c →
        ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
          c'.edges.toFinset ≠ c.edges.toFinset := by
  sorry

end LovaszPlummerConjecture

theorem LovaszPlummerConjecture.sheehan_conjecture.disproof : ¬ (type_of% @LovaszPlummerConjecture.sheehan_conjecture) := sorry
