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
# Octal games

An octal game is an impartial game played with heaps of tokens. A move selects one heap and
removes $k \ge 0$ tokens from it, leaving either no heap, one smaller non-empty heap, or two
non-empty heaps. Which of these are allowed for each $k$ is recorded by the octal code
$d_0.d_1 d_2 d_3 \ldots$ of the game: the digit $d_k \in \{0, \ldots, 7\}$ is the sum of
$1$ if removing $k$ tokens may leave no heap, $2$ if it may leave one heap, and $4$ if it may
leave two heaps. Since removing no tokens can only be a splitting move, $d_0 \in \{0, 4\}$.
The game is *finite* if only finitely many digits are non-zero.

By the Sprague–Grundy theorem a heap of $n$ tokens is equivalent to a nim heap of size
$\mathcal{G}(n)$, and the sequence $\mathcal{G}(0), \mathcal{G}(1), \ldots$ is the
*nim-sequence* of the game (in normal play). Every finite octal game analysed so far has an
ultimately periodic nim-sequence, and Richard Guy asked whether this always holds.

*References:*
- [Wikipedia, Octal game](https://en.wikipedia.org/wiki/octal_game)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- Berlekamp, Conway, Guy, *Winning Ways for your Mathematical Plays*, Chapter 4.
- R. K. Guy, *Unsolved problems in combinatorial games*, in: R. J. Nowakowski (ed.),
  *Games of No Chance*, MSRI Publications 29, Cambridge University Press, 1996.
-/

/-- An octal game, given by its octal code $d_0.d_1 d_2 d_3 \ldots$. The digit `digit k`
is the sum of `1` if a heap of exactly `k` tokens may be removed entirely, `2` if `k` tokens
may be removed from a larger heap leaving one heap, and `4` if `k` tokens may be removed from
a heap and the remainder split into two non-empty heaps. -/
structure OctalGame where
  /-- The digit $d_k$ of the octal code, for `k = 0, 1, 2, …`. -/
  digit : ℕ → Fin 8
  /-- Removing no tokens can only be a splitting move, so $d_0 \in \{0, 4\}$. -/
  digit_zero : digit 0 = 0 ∨ digit 0 = 4

namespace OctalGame

/-- An octal game is *finite* if only finitely many digits of its code are non-zero. -/
def IsFinite (G : OctalGame) : Prop := {k | G.digit k ≠ 0}.Finite

/-- Removing `k` tokens may leave no heap: the `1` bit of $d_k$ is set. -/
def CanTakeAll (G : OctalGame) (k : ℕ) : Prop := (G.digit k : ℕ).testBit 0

/-- Removing `k` tokens may leave one non-empty heap: the `2` bit of $d_k$ is set. -/
def CanLeaveOne (G : OctalGame) (k : ℕ) : Prop := (G.digit k : ℕ).testBit 1

/-- Removing `k` tokens may leave two non-empty heaps: the `4` bit of $d_k$ is set. -/
def CanSplit (G : OctalGame) (k : ℕ) : Prop := (G.digit k : ℕ).testBit 2

/-- The nim-sequence $\mathcal{G}(0), \mathcal{G}(1), \ldots$ of the game in normal play:
`nimSequence G n` is the nim-value (Sprague–Grundy value) of a single heap of `n` tokens.
It is the minimal excluded value of the nim-values of the positions reachable in one move,
where the empty position has nim-value `0`, a single heap of `m` tokens has nim-value
$\mathcal{G}(m)$, and two heaps of `a` and `b` tokens have nim-value
$\mathcal{G}(a) \oplus \mathcal{G}(b)$ (nim-sum, i.e. bitwise xor).

The arithmetic side conditions of the one-heap and two-heap moves are bound as (anonymous)
proof terms so that the recursion is seen to terminate. -/
noncomputable def nimSequence (G : OctalGame) (n : ℕ) : ℕ :=
  sInf {v |
    -- remove all `n` tokens of the heap, leaving no heap
    (0 < n ∧ G.CanTakeAll n ∧ v = 0) ∨
    -- remove `k` tokens, leaving one heap of `m` tokens
    (∃ k m, ∃ _ : 0 < k ∧ 0 < m ∧ m + k = n, G.CanLeaveOne k ∧ v = nimSequence G m) ∨
    -- remove `k` tokens, splitting the remainder into heaps of `a` and `b` tokens
    (∃ k a b, ∃ _ : 0 < a ∧ 0 < b ∧ a + b + k = n, G.CanSplit k ∧
      v = nimSequence G a ^^^ nimSequence G b)}ᶜ
termination_by n
decreasing_by all_goals omega

/-- Nim, with octal code `0.333…`. -/
def nim : OctalGame where
  digit k := if k = 0 then 0 else 3
  digit_zero := by simp

/-- Kayles, with octal code `0.77`. -/
def kayles : OctalGame where
  digit k := if k = 1 ∨ k = 2 then 7 else 0
  digit_zero := by simp

/-- **Guy's problem on octal games.**
Are the nim-sequences of all finite octal games eventually periodic? That is, does every
octal game with only finitely many non-zero digits have a nim-sequence
$\mathcal{G}(0), \mathcal{G}(1), \ldots$ for which there are $N$ and $p \ge 1$ with
$\mathcal{G}(n + p) = \mathcal{G}(n)$ for all $n \ge N$? -/
theorem octal_game :
    ∀ G : OctalGame, G.IsFinite →
      ∃ N p, 0 < p ∧ ∀ n ≥ N, G.nimSequence (n + p) = G.nimSequence n := by
  sorry

end OctalGame

theorem OctalGame.octal_game.disproof : ¬ (type_of% @OctalGame.octal_game) := sorry
