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
# Vertex coloring game: more colors for Alice

The vertex coloring game (Brams 1981, Bodlaender 1991) is played by Alice and Bob on a finite
simple graph $G$ with a fixed set of $k$ colors. The rules are:

* Alice moves first, and the players alternate turns; passing is not allowed.
* On each turn, the player chooses an uncolored vertex $v$ and a color that does not appear on
  any neighbor of $v$, and colors $v$ with it (so the coloring stays proper).
* If some uncolored vertex has every color on its neighborhood, it can never be colored and Bob
  wins.
* If every vertex gets colored, Alice wins.

The game chromatic number $\chi_g(G)$ is the least $k$ for which Alice has a winning strategy.

This file models a position as a partial coloring `V → Option (Fin k)` and defines the predicate
`AliceWinsFrom G c p`, meaning that Alice can force a win from position `c` with player `p` to
move. It is the usual backward-induction characterisation of having a winning strategy in a
finite two-player game of perfect information: Alice needs one legal move leading to a winning
position, Bob must have a legal move and all of his legal moves must lead to winning positions,
and a completely colored position is won for Alice. Since colors are never removed, an
uncolorable vertex stays uncolorable, so this agrees with the rule that Bob wins as soon as such
a vertex appears (see `not_aliceWinsFrom_of_isBlocked`).

The open problem asks whether having more colors can only help Alice.

*References:*
- [Wikipedia, Graph coloring game](https://en.wikipedia.org/wiki/graph_coloring_game)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- H. L. Bodlaender, *On the complexity of some coloring games*, Graph-Theoretic Concepts in
  Computer Science (WG 1990), LNCS 484, Springer, 1991,
  [doi:10.1007/3-540-53832-1_29](https://doi.org/10.1007/3-540-53832-1_29).
-/

namespace VertexColoringGame

/-- The two players of the vertex coloring game. -/
inductive Player
  | alice
  | bob

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) {k : ℕ}

/-- `IsLegalMove G c v i` says that, in the partial coloring `c` of the vertices of `G` with the
colors `Fin k`, coloring the vertex `v` with the color `i` is a legal move: `v` is uncolored and
no neighbor of `v` has color `i`. -/
def IsLegalMove (c : V → Option (Fin k)) (v : V) (i : Fin k) : Prop :=
  c v = none ∧ ∀ w, G.Adj v w → c w ≠ some i

/-- `AliceWinsFrom G c p` says that Alice can force a win in the vertex coloring game on `G`
from the partial coloring `c` when it is player `p`'s turn to move:
* if every vertex is colored, Alice has won;
* on Alice's turn, some legal move leads to a position from which Alice can force a win;
* on Bob's turn, Bob has a legal move and every legal move leads to a position from which Alice
  can force a win. -/
inductive AliceWinsFrom : (V → Option (Fin k)) → Player → Prop
  | complete {c : V → Option (Fin k)} {p : Player} (h : ∀ v, (c v).isSome) : AliceWinsFrom c p
  | alice {c : V → Option (Fin k)} (v : V) (i : Fin k) (hvi : IsLegalMove G c v i)
      (h : AliceWinsFrom (Function.update c v (some i)) .bob) : AliceWinsFrom c .alice
  | bob {c : V → Option (Fin k)} (hne : ∃ v i, IsLegalMove G c v i)
      (h : ∀ v i, IsLegalMove G c v i → AliceWinsFrom (Function.update c v (some i)) .alice) :
      AliceWinsFrom c .bob

variable (k) in
/-- `AliceHasWinningStrategy G k` says that Alice has a winning strategy for the vertex coloring
game on `G` with `k` colors: she can force a win from the empty coloring, moving first. -/
def AliceHasWinningStrategy : Prop :=
  AliceWinsFrom G (fun _ : V => (none : Option (Fin k))) .alice

/-- `IsBlocked G c v` says that the vertex `v` is uncolored in `c` and every color appears on a
neighbor of `v`, so that `v` can never be colored properly. -/
def IsBlocked (c : V → Option (Fin k)) (v : V) : Prop :=
  c v = none ∧ ∀ i : Fin k, ∃ w, G.Adj v w ∧ c w = some i

variable {G} in
/-- A legal move never unblocks a vertex. -/
@[category API, AMS 5 91]
theorem IsBlocked.update {c : V → Option (Fin k)} {u : V} {j : Fin k} (huj : IsLegalMove G c u j)
    {v : V} (hv : IsBlocked G c v) : IsBlocked G (Function.update c u (some j)) v := by
  obtain ⟨hu, hadj⟩ := huj
  obtain ⟨hv, hb⟩ := hv
  refine ⟨?_, fun i => ?_⟩
  · have huv : u ≠ v := by
      rintro rfl
      obtain ⟨w, hw, hcw⟩ := hb j
      exact hadj w hw hcw
    rw [Function.update_of_ne huv.symm, hv]
  · obtain ⟨w, hw, hcw⟩ := hb i
    have hwu : w ≠ u := by
      rintro rfl
      rw [hu] at hcw
      exact Option.some_ne_none i hcw.symm
    exact ⟨w, hw, by rw [Function.update_of_ne hwu, hcw]⟩

variable {G} in
/-- If some vertex is blocked, then Alice cannot win from `c`, whoever is to move. This is the
rule that Bob wins as soon as a vertex becomes uncolorable. -/
@[category API, AMS 5 91]
theorem not_aliceWinsFrom_of_isBlocked {c : V → Option (Fin k)} {v : V} (hv : IsBlocked G c v)
    (p : Player) : ¬ AliceWinsFrom G c p := by
  intro h
  induction h with
  | complete h => simpa [hv.1] using h v
  | alice u j huj _ ih => exact ih (hv.update huj)
  | bob hne _ ih =>
    obtain ⟨u, j, huj⟩ := hne
    exact ih u j huj (hv.update huj)

/-- On a graph with no vertices, Alice wins with any number of colors. -/
@[category test, AMS 5 91]
theorem aliceHasWinningStrategy_of_isEmpty [IsEmpty V] (k : ℕ) : AliceHasWinningStrategy G k :=
  .complete fun v => isEmptyElim v

/-- On a graph with at least one vertex, Alice does not win with `0` colors. -/
@[category test, AMS 5 91]
theorem not_aliceHasWinningStrategy_zero [Nonempty V] : ¬ AliceHasWinningStrategy G 0 := by
  rintro (h | ⟨v, i, -, -⟩)
  · obtain ⟨v⟩ := ‹Nonempty V›
    simpa using h v
  · exact i.elim0

/-- Alice wins on a single vertex with one color. -/
@[category test, AMS 5 91]
theorem aliceHasWinningStrategy_bot_unit : AliceHasWinningStrategy (⊥ : SimpleGraph Unit) 1 :=
  .alice () 0 ⟨rfl, fun _ h => h.elim⟩ (.complete fun v => by simp)

/-- Alice does not win on a single edge with one color: after her first move the other vertex
has no legal color, so Bob wins. -/
@[category test, AMS 5 91]
theorem not_aliceHasWinningStrategy_top_fin_two :
    ¬ AliceHasWinningStrategy (⊤ : SimpleGraph (Fin 2)) 1 := by
  rintro (h | ⟨v, i, -, (h | - | ⟨⟨w, j, hw, hwj⟩, -⟩)⟩)
  · simpa using h 0
  · have := h (v + 1)
    simp at this
  · simp only [Function.update_apply, ne_eq] at hw hwj
    have hwv : w ≠ v := by rintro rfl; simp at hw
    have := hwj v (by simpa [SimpleGraph.top_adj] using hwv)
    simp [Fin.eq_zero i, Fin.eq_zero j] at this

/-- **More colors for Alice.** Suppose Alice has a winning strategy for the vertex coloring game
on a graph $G$ with $k$ colors. Does she have one for $k+1$ colors?

Here $G$ ranges over all finite simple graphs and $k$ over all natural numbers. The game uses the
standard conventions: Alice moves first, the players alternate without passing, each move
properly colors an uncolored vertex with one of exactly $k$ colors, and Alice wins if and only if
every vertex gets colored. Including $k = 0$ does not change the question: with $0$ colors Alice
wins only on the graph with no vertices, where she also wins with $1$ color (see
`aliceHasWinningStrategy_of_isEmpty` and `not_aliceHasWinningStrategy_zero`). -/
@[category research open, AMS 5 91]
theorem vertex_coloring_game : answer(sorry) ↔
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ),
      AliceHasWinningStrategy G k → AliceHasWinningStrategy G (k + 1) := by
  sorry

end VertexColoringGame
