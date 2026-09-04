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
# Grundy's game

Grundy's game is a two-player impartial game. The starting position is a single heap of
objects, and the players take turns splitting a single heap into two heaps of *different* sizes.
Under normal play, the last player able to move wins. Heaps of size at most two can not be split.

By the Sprague–Grundy theorem, a single heap of size $n$ is equivalent to a nim heap of size
$G(n)$, where the *nim-sequence* $G$ is given by $G(0) = G(1) = G(2) = 0$ and
$$G(n) = \operatorname{mex}\{G(a) \oplus G(b) : a + b = n,\ 1 \le a < b\},$$
with $\oplus$ the bitwise XOR (nim-sum) and $\operatorname{mex}$ the least natural number not in
the set. This is OEIS sequence A002188.

Berlekamp, Conway and Guy conjectured that this sequence is eventually periodic. Despite the
computation of the first $2^{35}$ values by Achim Flammenkamp, the question remains open.

*References:*
- [Grundy's game (Wikipedia)](https://en.wikipedia.org/wiki/Grundy%27s_game)
- [List of unsolved problems in mathematics (Wikipedia)](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [A002188 (OEIS)](https://oeis.org/A002188)
-/

namespace GrundysGame

/--
The nim-value (Sprague–Grundy value) $G(n)$ of a single heap of size $n$ in Grundy's game.

A move splits the heap into two heaps of sizes $a$ and $b$ with $a + b = n$ and $1 \le a < b$;
the resulting position has nim-value $G(a) \oplus G(b)$ (bitwise XOR). Then $G(n)$ is the minimum
excluded value of the nim-values of all positions reachable in one move, i.e. the least natural
number $v$ that is not of the form $G(a) \oplus G(b)$ for such a split. In particular
$G(0) = G(1) = G(2) = 0$, as heaps of size at most two admit no move.
-/
noncomputable def nimValue (n : ℕ) : ℕ :=
  sInf {v : ℕ | ∀ a b, 0 < a → a < b → a + b = n → nimValue a ^^^ nimValue b ≠ v}
termination_by n
decreasing_by all_goals omega

/-- `nimValue n = v` as soon as `v` is not the nim-value of any option of a heap of size `n`,
while every `w < v` is. -/
@[category API, AMS 5 91]
theorem nimValue_eq_of {n v : ℕ}
    (hv : ∀ a b, 0 < a → a < b → a + b = n → nimValue a ^^^ nimValue b ≠ v)
    (hlt : ∀ w < v, ∃ a b, 0 < a ∧ a < b ∧ a + b = n ∧ nimValue a ^^^ nimValue b = w) :
    nimValue n = v := by
  rw [nimValue]
  refine le_antisymm (Nat.sInf_le hv) (le_csInf ⟨v, hv⟩ fun w hw => not_lt.1 fun h => ?_)
  obtain ⟨a, b, ha, hab, habn, hw'⟩ := hlt w h
  exact hw a b ha hab habn hw'

@[category test, AMS 5 91]
theorem nimValue_zero : nimValue 0 = 0 :=
  nimValue_eq_of (fun _ _ _ _ _ => by omega) (fun _ hw => by omega)

@[category test, AMS 5 91]
theorem nimValue_one : nimValue 1 = 0 :=
  nimValue_eq_of (fun _ _ _ _ _ => by omega) (fun _ hw => by omega)

@[category test, AMS 5 91]
theorem nimValue_two : nimValue 2 = 0 :=
  nimValue_eq_of (fun _ _ _ _ _ => by omega) (fun _ hw => by omega)

@[category test, AMS 5 91]
theorem nimValue_three : nimValue 3 = 1 := by
  refine nimValue_eq_of (fun a b ha hab habn => ?_) (fun w hw => ?_)
  · obtain ⟨rfl, rfl⟩ : a = 1 ∧ b = 2 := by omega
    simp [nimValue_one, nimValue_two]
  · obtain rfl : w = 0 := by omega
    exact ⟨1, 2, by omega, by omega, rfl, by simp [nimValue_one, nimValue_two]⟩

@[category test, AMS 5 91]
theorem nimValue_four : nimValue 4 = 0 := by
  refine nimValue_eq_of (fun a b ha hab habn => ?_) (fun w hw => by omega)
  obtain ⟨rfl, rfl⟩ : a = 1 ∧ b = 3 := by omega
  simp [nimValue_one, nimValue_three]

@[category test, AMS 5 91]
theorem nimValue_five : nimValue 5 = 2 := by
  refine nimValue_eq_of (fun a b ha hab habn => ?_) (fun w hw => ?_)
  · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (a = 1 ∧ b = 4) ∨ (a = 2 ∧ b = 3) := by omega
    · simp [nimValue_one, nimValue_four]
    · simp [nimValue_two, nimValue_three]
  · obtain rfl | rfl : w = 0 ∨ w = 1 := by omega
    · exact ⟨1, 4, by omega, by omega, rfl, by simp [nimValue_one, nimValue_four]⟩
    · exact ⟨2, 3, by omega, by omega, rfl, by simp [nimValue_two, nimValue_three]⟩

/--
**Grundy's game.** Is the nim-sequence of Grundy's game eventually periodic?

That is, do there exist a period $p > 0$ and a threshold $N$ such that $G(n + p) = G(n)$ for all
$n \ge N$, where $G(n)$ is the nim-value of a single heap of size $n$ in Grundy's game?
Berlekamp, Conway and Guy conjectured that the answer is yes.
-/
@[category research open, AMS 5 91]
theorem grundys_game :
    answer(sorry) ↔ ∃ p > 0, ∃ N, ∀ n ≥ N, nimValue (n + p) = nimValue n := by
  sorry

end GrundysGame
