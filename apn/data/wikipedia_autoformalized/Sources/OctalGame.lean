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

/-- The empty heap has no moves, so its nim-value is `0`. -/
@[category API, AMS 91]
theorem nimSequence_zero (G : OctalGame) : G.nimSequence 0 = 0 := by
  rw [nimSequence, Nat.sInf_eq_zero]
  left
  rintro (⟨h, -⟩ | ⟨k, m, ⟨hk, hm, h⟩, -⟩ | ⟨k, a, b, ⟨ha, hb, h⟩, -⟩) <;> omega

/-- Nim, with octal code `0.333…`. -/
def nim : OctalGame where
  digit k := if k = 0 then 0 else 3
  digit_zero := by simp

/-- Nim is not a finite octal game. -/
@[category test, AMS 91]
theorem nim_not_isFinite : ¬ nim.IsFinite := by
  intro h
  have : {k | nim.digit k ≠ 0} = Set.Ioi 0 := by
    ext k
    simp [nim, Nat.pos_iff_ne_zero]
  rw [IsFinite, this] at h
  exact Set.Ioi_infinite 0 h

/-- The nim-value of a nim heap of `n` tokens is `n`. -/
@[category test, AMS 91]
theorem nim_nimSequence (n : ℕ) : nim.nimSequence n = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [nimSequence]
  apply IsLeast.csInf_eq
  constructor
  · rintro (⟨h₀, -, h⟩ | ⟨k, m, ⟨hk, hm, h⟩, -, hv⟩ |
      ⟨k, a, b, ⟨ha, hb, h⟩, hs, -⟩)
    · omega
    · rw [ih m (by omega)] at hv; omega
    · simp only [CanSplit, nim] at hs
      split_ifs at hs <;> exact absurd hs (by decide)
  · intro v hv
    by_contra hlt
    push_neg at hlt
    apply hv
    rcases v with _ | v
    · refine Or.inl ⟨hlt, ?_, rfl⟩
      simp only [CanTakeAll, nim, hlt.ne']
      decide
    · refine Or.inr (Or.inl ⟨n - (v + 1), v + 1, ⟨by omega, by omega, by omega⟩, ?_,
        (ih (v + 1) hlt).symm⟩)
      have : n - (v + 1) ≠ 0 := by omega
      simp only [CanLeaveOne, nim, this]
      decide

/-- Kayles, with octal code `0.77`. -/
def kayles : OctalGame where
  digit k := if k = 1 ∨ k = 2 then 7 else 0
  digit_zero := by simp

/-- Kayles is a finite octal game. -/
@[category test, AMS 91]
theorem kayles_isFinite : kayles.IsFinite := by
  refine (Set.finite_le_nat 2).subset fun k hk => ?_
  simp only [kayles, Set.mem_setOf_eq, ne_eq, ite_eq_right_iff, Classical.not_imp] at hk
  show k ≤ 2
  omega

@[category API, AMS 91]
lemma kayles_not_move {k : ℕ} (h : ¬ (k = 1 ∨ k = 2)) :
    ¬ kayles.CanTakeAll k ∧ ¬ kayles.CanLeaveOne k ∧ ¬ kayles.CanSplit k := by
  simp [CanTakeAll, CanLeaveOne, CanSplit, kayles, h]

@[category API, AMS 91]
lemma kayles_move {k : ℕ} (h : k = 1 ∨ k = 2) :
    kayles.CanTakeAll k ∧ kayles.CanLeaveOne k ∧ kayles.CanSplit k := by
  simp only [CanTakeAll, CanLeaveOne, CanSplit, kayles, h, if_true]
  decide

/-- The nim-sequence of Kayles starts `0, 1, 2, 3, …`. -/
@[category test, AMS 91]
theorem kayles_nimSequence_one : kayles.nimSequence 1 = 1 := by
  rw [nimSequence]
  apply IsLeast.csInf_eq
  constructor
  · rintro (⟨-, -, h⟩ | ⟨k, m, ⟨hk, hm, h⟩, -⟩ | ⟨k, a, b, ⟨ha, hb, h⟩, -⟩) <;>
      omega
  · intro v hv
    by_contra hlt
    obtain rfl : v = 0 := by omega
    exact hv (Or.inl ⟨by omega, (kayles_move (by omega)).1, rfl⟩)

@[category test, AMS 91]
theorem kayles_nimSequence_two : kayles.nimSequence 2 = 2 := by
  rw [nimSequence]
  apply IsLeast.csInf_eq
  constructor
  · rintro (⟨-, -, h⟩ | ⟨k, m, ⟨hk, hm, h⟩, -, hv⟩ |
      ⟨k, a, b, ⟨ha, hb, h⟩, hs, -⟩)
    · omega
    · obtain rfl : m = 1 := by omega
      rw [kayles_nimSequence_one] at hv
      omega
    · obtain rfl : k = 0 := by omega
      exact (kayles_not_move (by omega)).2.2 hs
  · intro v hv
    by_contra hlt
    apply hv
    obtain rfl | rfl : v = 0 ∨ v = 1 := by omega
    · exact Or.inl ⟨by omega, (kayles_move (by omega)).1, rfl⟩
    · exact Or.inr (Or.inl ⟨1, 1, ⟨by omega, by omega, by omega⟩,
        (kayles_move (by omega)).2.1, kayles_nimSequence_one.symm⟩)

/-- A heap of three tokens in Kayles has nim-value `3`; this exercises the splitting move,
whose option `1 + 1` has nim-value $\mathcal{G}(1) \oplus \mathcal{G}(1) = 0$. -/
@[category test, AMS 91]
theorem kayles_nimSequence_three : kayles.nimSequence 3 = 3 := by
  rw [nimSequence]
  apply IsLeast.csInf_eq
  constructor
  · rintro (⟨-, -, h⟩ | ⟨k, m, ⟨hk, hm, h⟩, hl, hv⟩ |
      ⟨k, a, b, ⟨ha, hb, h⟩, hs, hv⟩)
    · omega
    · obtain rfl | rfl : m = 1 ∨ m = 2 := by omega
      · rw [kayles_nimSequence_one] at hv; omega
      · rw [kayles_nimSequence_two] at hv; omega
    · obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
      · exact (kayles_not_move (by omega)).2.2 hs
      · obtain ⟨rfl, rfl⟩ : a = 1 ∧ b = 1 := by omega
        rw [kayles_nimSequence_one] at hv
        exact absurd hv (by decide)
  · intro v hv
    by_contra hlt
    apply hv
    obtain rfl | rfl | rfl : v = 0 ∨ v = 1 ∨ v = 2 := by omega
    · exact Or.inr (Or.inr ⟨1, 1, 1, ⟨by omega, by omega, by omega⟩,
        (kayles_move (by omega)).2.2, by rw [kayles_nimSequence_one]; rfl⟩)
    · exact Or.inr (Or.inl ⟨2, 1, ⟨by omega, by omega, by omega⟩,
        (kayles_move (by omega)).2.1, kayles_nimSequence_one.symm⟩)
    · exact Or.inr (Or.inl ⟨1, 2, ⟨by omega, by omega, by omega⟩,
        (kayles_move (by omega)).2.1, kayles_nimSequence_two.symm⟩)

/-- **Guy's problem on octal games.**
Are the nim-sequences of all finite octal games eventually periodic? That is, does every
octal game with only finitely many non-zero digits have a nim-sequence
$\mathcal{G}(0), \mathcal{G}(1), \ldots$ for which there are $N$ and $p \ge 1$ with
$\mathcal{G}(n + p) = \mathcal{G}(n)$ for all $n \ge N$? -/
@[category research open, AMS 91]
theorem octal_game :
    answer(sorry) ↔ ∀ G : OctalGame, G.IsFinite →
      ∃ N p, 0 < p ∧ ∀ n ≥ N, G.nimSequence (n + p) = G.nimSequence n := by
  sorry

end OctalGame
