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
# Meyniel's conjecture on the cop number

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Cop_number)
* [Fr87] Frankl, P. (1987). "Cops and robbers in graphs with large girth and Cayley graphs."
  *Discrete Appl. Math.* 17, pp. 301--305.
* [NW83] Nowakowski, R. and Winkler, P. (1983). "Vertex-to-vertex pursuit in a graph."
  *Discrete Math.* 43, pp. 235--239.
* [SS11] Scott, A. and Sudakov, B. (2011). "A bound for the cops and robbers problem."
  *SIAM J. Discrete Math.* 25, pp. 1438--1442.
* [BB12] Baird, W. and Bonato, A. (2012). "Meyniel's conjecture on the cop number: a survey."
  *J. Comb.* 3, pp. 225--238.
-/

open Filter

namespace MeynielConjecture

variable {V : Type*}

/-- A **move** in the cops-and-robbers game: stay put, or slide along an edge. -/
def Step (G : SimpleGraph V) (u v : V) : Prop :=
  u = v ∨ G.Adj u v

/-- `CopsCatchWithin G k m c r`: with `k` cops at positions `c`, the robber at `r`, and the cops
to move, the cops can guarantee to catch the robber within `m` further rounds. In each round
every cop moves (or stays), catching the robber if a cop reaches the robber's vertex, and then
the robber moves (or stays). -/
def CopsCatchWithin (G : SimpleGraph V) (k : ℕ) : ℕ → (Fin k → V) → V → Prop
  | 0, c, r => ∃ i, c i = r
  | m + 1, c, r =>
      (∃ i, c i = r) ∨
        ∃ c' : Fin k → V, (∀ i, Step G (c i) (c' i)) ∧
          ((∃ i, c' i = r) ∨ ∀ r', Step G r r' → CopsCatchWithin G k m c' r')

/-- `k` cops have a winning strategy on `G`: they can choose starting positions such that,
wherever the robber starts, they catch the robber in finitely many rounds. -/
def CopsWin (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : Fin k → V, ∀ r : V, ∃ m, CopsCatchWithin G k m c r

/-- The **cop number** `c(G)`: the least number of cops that can guarantee to catch the
robber on `G`. -/
noncomputable def copNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | CopsWin G k}

/--
**The soft Meyniel conjecture.**

There are constants `ε, C > 0` such that every connected graph on `n` vertices has cop number
at most `C n^(1 - ε)`. Even this weakening of Meyniel's conjecture is open; no bound of the
form `O(n^(1 - ε))` is known. See [BB12].
-/
theorem meyniel_conjecture.variants.soft :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      (copNumber G : ℝ) ≤ C * (Fintype.card V : ℝ) ^ ((1 : ℝ) - ε) := by
  sorry

end MeynielConjecture

theorem MeynielConjecture.meyniel_conjecture.variants.soft.disproof : ¬ (type_of% @MeynielConjecture.meyniel_conjecture.variants.soft) := sorry
