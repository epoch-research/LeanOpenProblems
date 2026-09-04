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

/--
**Meyniel's conjecture.** The cop number of a connected graph on $n$ vertices is $O(\sqrt n)$:
there is a constant $d > 0$ such that every finite connected simple graph $G$ on $n$ vertices
satisfies $c(G) \le d \sqrt n$.

The constant $d$ is independent of the graph. Since $c(G) \le n$ always holds, it makes no
difference whether the bound is required for all $n$ or only for all sufficiently large $n$.
-/
theorem cop_number :
    ∃ d : ℝ, 0 < d ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      (copNumber G : ℝ) ≤ d * √(Fintype.card V) := by
  sorry

end CopNumber

theorem CopNumber.cop_number.disproof : ¬ (type_of% @CopNumber.cop_number) := sorry
