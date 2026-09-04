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
# Komi

In the game of Go, *komi* is the number of points added to White's score to compensate for
Black moving first. A *perfect* komi is a value that makes the game end in a draw (*jigo*) under
perfect play by both sides. Wikipedia's list of unsolved problems asks:

> What is the perfect value of komi?

The answer depends on the ruleset, which the source does not fix. We use the Tromp–Taylor rules,
a complete and precise ruleset with area scoring: stones are placed on the empty points of a
square grid; after a move, first the opponent's and then one's own stones without liberties are
removed; a move may not recreate an earlier grid colouring (positional superko); the game ends
after two consecutive passes; a player's score is the number of points of their colour plus the
number of empty points that reach only their colour. We also allow the variant in which suicide
(a move that removes one's own stones) is forbidden, as in most other area scoring rulesets.

Under perfect play, Black can force a final score margin of at least some value $V$, and White
can force a margin of at most $V$; this minimax value $V$ (an integer) is the perfect komi:
with komi $V$ perfect play ends in *jigo*, with any other komi one side can force a win.
Under area scoring, statistics from professional and computer play suggest that the perfect komi
is $7$.

*References:*
- [Wikipedia, Komi (Go)](https://en.wikipedia.org/wiki/Komi_%28Go%29)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [J. Tromp, B. Taylor, The logical rules of Go](https://tromp.github.io/go.html)
-/

namespace Komi

/-- The two players, identified with the colour of their stones. -/
inductive Color
  | black
  | white
  deriving DecidableEq, Fintype

/-- The opponent of a player. -/
def Color.opp : Color → Color
  | black => white
  | white => black

/-- The points of an `n × n` Go board. -/
abbrev Point (n : ℕ) := Fin n × Fin n

/-- The grid graph of the board: two points are adjacent if they are horizontal or vertical
neighbours. -/
abbrev grid (n : ℕ) : SimpleGraph (Point n) :=
  SimpleGraph.pathGraph n □ SimpleGraph.pathGraph n

/-- A position colours each point of the board black, white or empty (`none`). -/
abbrev Position (n : ℕ) := Point n → Option Color

namespace Position

variable {n : ℕ} (pos : Position n)

/-- `pos.Chain p q` holds if `q` can be reached from `p` by a path of adjacent points all of
the same colour as `p`. -/
def Chain (p q : Point n) : Prop :=
  Relation.ReflTransGen (fun a b => (grid n).Adj a b ∧ pos b = pos p) p q

/-- A point `p` not coloured `c` *reaches* `c` if there is a path of adjacent points of `p`'s
colour from `p` to a point of colour `c`. -/
def Reaches (p : Point n) (c : Option Color) : Prop :=
  pos p ≠ c ∧ ∃ q r, pos.Chain p q ∧ (grid n).Adj q r ∧ pos r = c

open scoped Classical in
/-- Clearing a colour `c`: emptying all points of colour `c` that do not reach empty. -/
noncomputable def clear (c : Color) : Position n :=
  fun p => if pos p = some c ∧ ¬ pos.Reaches p none then none else pos p

/-- The position obtained when player `c` plays at the point `p`: colour `p` with `c`, then clear
the opponent's colour, then clear one's own colour. -/
noncomputable def play (c : Color) (p : Point n) : Position n :=
  (Position.clear (Function.update pos p (some c)) c.opp).clear c

open scoped Classical in
/-- The (area) score of player `c`: the number of points of colour `c` plus the number of empty
points that reach only colour `c`. -/
noncomputable def score (c : Color) : ℕ :=
  (Finset.univ.filter fun p => pos p = some c ∨
    (pos p = none ∧ pos.Reaches p (some c) ∧ ¬ pos.Reaches p (some c.opp))).card

/-- Black's score minus White's score. -/
noncomputable def margin : ℤ :=
  pos.score .black - pos.score .white

end Position

/-- The parameters of the ruleset: the side length of the board, and whether suicide (a move
that removes one's own stones) is allowed. -/
structure Rules where
  /-- The side length of the (square) board. -/
  size : ℕ
  /-- Whether a move that removes one's own stones is allowed. -/
  suicideAllowed : Bool

/-- The Tromp–Taylor rules on the standard `19 × 19` board; suicide is allowed. -/
def Rules.trompTaylor : Rules where
  size := 19
  suicideAllowed := true

/-- The state of a game: the current position, the player to move, the set of all positions
that have occurred so far (including the current one) and the number of consecutive passes
that have just been made. -/
structure State (n : ℕ) where
  /-- The current position. -/
  pos : Position n
  /-- The player to move. -/
  toMove : Color
  /-- All positions that have occurred so far, including the current one. -/
  history : Finset (Position n)
  /-- The number of consecutive passes immediately preceding this state. -/
  passes : ℕ
  deriving DecidableEq

namespace State

variable {n : ℕ}

/-- The initial state: the empty board, Black to move. -/
def initial (n : ℕ) : State n where
  pos := fun _ => none
  toMove := .black
  history := {fun _ => none}
  passes := 0

/-- The game ends after two consecutive passes. -/
def IsTerminal (s : State n) : Prop := 2 ≤ s.passes

instance (s : State n) : Decidable s.IsTerminal := inferInstanceAs (Decidable (2 ≤ s.passes))

/-- The state after the player to move passes. -/
def pass (s : State n) : State n :=
  { s with toMove := s.toMove.opp, passes := s.passes + 1 }

/-- The state after the player to move plays at `p`. -/
noncomputable def move (s : State n) (p : Point n) : State n where
  pos := s.pos.play s.toMove p
  toMove := s.toMove.opp
  history := insert (s.pos.play s.toMove p) s.history
  passes := 0

/-- Playing at `p` is legal if `p` is empty, the resulting position has not occurred before
(positional superko) and, unless suicide is allowed, the played stone is not removed. -/
def IsLegal (r : Rules) (s : State n) (p : Point n) : Prop :=
  s.pos p = none ∧ s.pos.play s.toMove p ∉ s.history ∧
    (r.suicideAllowed ∨ s.pos.play s.toMove p p = some s.toMove)

open scoped Classical in
/-- The states that can be reached in one turn: by passing or by a legal move. -/
noncomputable def options (r : Rules) (s : State n) : Finset (State n) :=
  insert s.pass ((Finset.univ.filter (s.IsLegal r)).image s.move)

/-- A measure that decreases along every turn of a game that has not ended. -/
def measure (s : State n) : ℕ :=
  2 * (Fintype.card (Position n) - s.history.card) + (2 - s.passes)

/-- Passing is always an option. -/
theorem pass_mem_options (r : Rules) (s : State n) : s.pass ∈ s.options r :=
  Finset.mem_insert_self _ _

/-- Every turn of a game that has not ended decreases `measure`. -/
theorem measure_lt_of_mem_options {r : Rules} {s t : State n} (ht : t ∈ s.options r)
    (hs : ¬ s.IsTerminal) : t.measure < s.measure := by
  simp only [IsTerminal, not_le] at hs
  simp only [options, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and] at ht
  obtain rfl | ⟨p, hp, rfl⟩ := ht
  · simp only [measure, pass]
    omega
  · have h₁ := Finset.card_insert_of_notMem hp.2.1
    have h₂ := Finset.card_le_univ (insert (s.pos.play s.toMove p) s.history)
    simp only [measure, move]
    omega

/-- The minimax value, from state `s`, of Black's final score margin: Black maximises it and
White minimises it. -/
noncomputable def value (r : Rules) (s : State n) : ℤ :=
  if s.IsTerminal then s.pos.margin
  else
    have hne : (s.options r).attach.Nonempty :=
      Finset.attach_nonempty_iff.2 ⟨_, s.pass_mem_options r⟩
    if s.toMove = .black then
      (s.options r).attach.sup' hne fun t => value r t.1
    else
      (s.options r).attach.inf' hne fun t => value r t.1
termination_by s.measure
decreasing_by all_goals exact measure_lt_of_mem_options t.2 ‹_›

end State

/-- The perfect komi under the rules `r`: the minimax value of Black's final score margin from
the empty board with Black to move. With this komi, perfect play by both sides ends in *jigo*. -/
noncomputable def perfectKomi (r : Rules) : ℤ :=
  State.value r (State.initial r.size)

/--
Statistics from professional and computer play suggest that under area scoring the perfect komi
is $7$: under the Tromp–Taylor rules on the standard `19 × 19` board, the minimax value of
Black's final score margin is $7$.
-/
theorem komi.variants.eq_seven : perfectKomi .trompTaylor = 7 := by
  sorry

end Komi

theorem Komi.komi.variants.eq_seven.disproof : ¬ (type_of% @Komi.komi.variants.eq_seven) := sorry
