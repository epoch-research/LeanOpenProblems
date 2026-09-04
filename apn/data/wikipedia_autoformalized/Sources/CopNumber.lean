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
# Cop number

The game of *Cops and Robbers* is played on a finite graph $G$ by a set of $k$ cops and a
single robber, who occupy vertices of $G$. First the cops are placed on vertices of $G$ (several
cops may share a vertex), then the robber is placed on a vertex. Afterwards the players alternate
turns, cops first. On the cops' turn each cop either stays put or moves to an adjacent vertex; on
the robber's turn the robber either stays put or moves to an adjacent vertex. The cops win if,
after finitely many rounds, some cop occupies the same vertex as the robber; otherwise the
robber wins. The *cop number* $c(G)$ is the least $k$ such that $k$ cops have a winning
strategy on $G$.

**Meyniel's conjecture** (1985, reported by Frankl) states that the cop number of every
connected $n$-vertex graph is $O(\sqrt n)$.

*References:*
- [Wikipedia: Cop number](https://en.wikipedia.org/wiki/cop_number)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [BB13] W. Baird, A. Bonato, *Meyniel's conjecture on the cop number: a survey*,
  Journal of Combinatorics 3 (2012), 225–238. [arXiv:1308.3385](https://arxiv.org/abs/1308.3385)
- [Fra87] P. Frankl, *Cops and robbers in graphs with large girth and Cayley graphs*,
  Discrete Applied Mathematics 17 (1987), 301–305.
-/

namespace CopNumber

variable {V : Type*} (G : SimpleGraph V)

/--
`CopsWin G c r` says that, in the game of Cops and Robbers on `G` with the `k` cops standing on
the vertices `c 0, …, c (k - 1)`, the robber standing on `r`, and the cops to move, the cops can
force a capture in finitely many rounds.

On their turn the cops move to positions `c'`, where each cop either stays put or moves to an
adjacent vertex. If some cop now stands on the robber's vertex, the robber is captured. Otherwise
the robber either stays put or moves to an adjacent vertex `r'`, and the cops must be able to
force a capture from the position `(c', r')`.
-/
inductive CopsWin {k : ℕ} : (Fin k → V) → V → Prop
  /-- The cops move to `c'` and one of them lands on the robber. -/
  | capture {c : Fin k → V} {r : V} (c' : Fin k → V)
      (hc' : ∀ i, c' i = c i ∨ G.Adj (c i) (c' i)) (h : ∃ i, c' i = r) :
      CopsWin c r
  /-- The cops move to `c'`, and whatever the robber does next, the cops can still force a
  capture. -/
  | step {c : Fin k → V} {r : V} (c' : Fin k → V)
      (hc' : ∀ i, c' i = c i ∨ G.Adj (c i) (c' i))
      (h : ∀ r', (r' = r ∨ G.Adj r r') → CopsWin c' r') :
      CopsWin c r

/--
`k` cops have a winning strategy on `G`: the cops can be placed on vertices `c 0, …, c (k - 1)`
of `G` (repetitions allowed) so that, wherever the robber then places himself, the cops can
force a capture.
-/
def CopsCanWin (k : ℕ) : Prop :=
  ∃ c : Fin k → V, ∀ r : V, CopsWin G c r

/--
The cop number $c(G)$ of a graph `G`: the least number of cops that have a winning strategy in
the game of Cops and Robbers on `G`.

For a finite graph this is well defined, since placing one cop on every vertex wins at once.
(For an infinite graph on which no finite number of cops wins, the `sInf` is `0` by convention;
this case is not relevant here.)
-/
noncomputable def copNumber : ℕ :=
  sInf {k | CopsCanWin G k}

/-- Cops standing on the robber's vertex win by passing. -/
@[category API, AMS 5]
theorem CopsWin.of_exists_eq {k : ℕ} {c : Fin k → V} {r : V} (h : ∃ i, c i = r) :
    CopsWin G c r :=
  .capture c (fun _ => Or.inl rfl) h

/-- One cop on every vertex wins immediately. -/
@[category API, AMS 5]
theorem copsCanWin_card [Fintype V] : CopsCanWin G (Fintype.card V) :=
  ⟨(Fintype.equivFin V).symm, fun r => .of_exists_eq G ⟨Fintype.equivFin V r, by simp⟩⟩

/-- The cop number of a finite graph is at most its number of vertices. -/
@[category API, AMS 5]
theorem copNumber_le_card [Fintype V] : copNumber G ≤ Fintype.card V :=
  Nat.sInf_le (copsCanWin_card G)

/-- Without cops, the robber is never captured. -/
@[category API, AMS 5]
theorem not_copsWin_zero (c : Fin 0 → V) (r : V) : ¬ CopsWin G c r := by
  intro h
  induction h with
  | capture _ _ h => exact h.elim fun i _ => i.elim0
  | @step _ r _ _ _ ih => exact ih r (Or.inl rfl)

/-- The cop number of a nonempty finite graph is positive. -/
@[category API, AMS 5]
theorem copNumber_pos [Fintype V] [Nonempty V] : 0 < copNumber G := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  have hmem : copNumber G ∈ {k | CopsCanWin G k} := Nat.sInf_mem ⟨_, copsCanWin_card G⟩
  rw [h0] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact not_copsWin_zero G c (Classical.arbitrary V) (hc _)

/-- A complete graph on at least one vertex has cop number `1`. -/
@[category test, AMS 5]
theorem copNumber_top [Fintype V] [Nonempty V] : copNumber (⊤ : SimpleGraph V) = 1 := by
  refine le_antisymm (Nat.sInf_le ?_) (copNumber_pos _)
  obtain ⟨v⟩ := ‹Nonempty V›
  refine ⟨fun _ => v, fun r => .capture (fun _ => r) (fun _ => ?_) ⟨0, rfl⟩⟩
  by_cases h : r = v
  · exact Or.inl h
  · exact Or.inr fun hv => h hv.symm

/-- In the graph without edges, the robber is safe on any vertex not occupied by a cop. -/
@[category API, AMS 5]
theorem not_copsWin_bot {k : ℕ} {c : Fin k → V} {r : V} (hr : r ∉ Set.range c) :
    ¬ CopsWin (⊥ : SimpleGraph V) c r := by
  intro h
  induction h with
  | @capture c r c' hc' h =>
    obtain ⟨i, hi⟩ := h
    exact hr ⟨i, ((hc' i).resolve_right (by simp)).symm.trans hi⟩
  | @step c r c' hc' _ ih =>
    exact ih r (Or.inl rfl) (by rwa [funext fun i => (hc' i).resolve_right (by simp)])

/-- The graph without edges on `n` vertices has cop number `n`. -/
@[category test, AMS 5]
theorem copNumber_bot [Fintype V] : copNumber (⊥ : SimpleGraph V) = Fintype.card V := by
  refine le_antisymm (copNumber_le_card _)
    (le_csInf ⟨_, copsCanWin_card _⟩ fun k ⟨c, hc⟩ => not_lt.1 fun hlt => ?_)
  obtain ⟨r, hr⟩ : ∃ r, r ∉ Set.range c := by
    by_contra hall
    push_neg at hall
    exact absurd (Fintype.card_le_of_surjective c hall) (by simpa using hlt)
  exact not_copsWin_bot hr (hc r)

/--
**Meyniel's conjecture.** The cop number of a connected graph on $n$ vertices is $O(\sqrt n)$:
there is a constant $d > 0$ such that every finite connected simple graph $G$ on $n$ vertices
satisfies $c(G) \le d \sqrt n$.

The constant $d$ is independent of the graph. Since $c(G) \le n$ always holds, it makes no
difference whether the bound is required for all $n$ or only for all sufficiently large $n$.
-/
@[category research open, AMS 5 91]
theorem cop_number :
    ∃ d : ℝ, 0 < d ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      (copNumber G : ℝ) ≤ d * √(Fintype.card V) := by
  sorry

end CopNumber
