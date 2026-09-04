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

/-- **More colors for Alice.** Suppose Alice has a winning strategy for the vertex coloring game
on a graph $G$ with $k$ colors. Does she have one for $k+1$ colors?

Here $G$ ranges over all finite simple graphs and $k$ over all natural numbers. The game uses the
standard conventions: Alice moves first, the players alternate without passing, each move
properly colors an uncolored vertex with one of exactly $k$ colors, and Alice wins if and only if
every vertex gets colored. Including $k = 0$ does not change the question: with $0$ colors Alice
wins only on the graph with no vertices, where she also wins with $1$ color (see
`aliceHasWinningStrategy_of_isEmpty` and `not_aliceHasWinningStrategy_zero`). -/
theorem vertex_coloring_game : 
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ),
      AliceHasWinningStrategy G k → AliceHasWinningStrategy G (k + 1) := by
  sorry

end VertexColoringGame

theorem VertexColoringGame.vertex_coloring_game.disproof : ¬ (type_of% @VertexColoringGame.vertex_coloring_game) := sorry
