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
# Maximum number of givens of a minimal Sudoku puzzle

A (classic) Sudoku puzzle is a partially filled $9 \times 9$ grid, divided into nine
$3 \times 3$ boxes. The filled cells are the *givens* (or *clues*). A *solution* of the puzzle
is a completion of the grid in which every row, every column and every box contains each of the
nine digits exactly once. A puzzle is *proper* if it has exactly one solution. A puzzle is
*minimal* if it is proper and no given can be removed without introducing additional solutions.

Wikipedia asks: what is the maximum number of givens for a minimal puzzle? The largest minimal
puzzle found so far has $40$ givens, and $40$ is believed to be the maximum.

*References:*
- [Wikipedia: Mathematics of Sudoku, Maximum number of givens](https://en.wikipedia.org/wiki/Mathematics_of_Sudoku%23Maximum_number_of_givens)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
-/

namespace MaximumNumberOfGivens

/-- A cell of the $9 \times 9$ Sudoku grid, given by its row and its column. -/
abbrev Cell := Fin 9 × Fin 9

/-- Two cells *see* each other if they lie in the same row, in the same column, or in the same
$3 \times 3$ box. The box of a cell is determined by the quotients of its row and column by
$3$. -/
def Sees (c d : Cell) : Prop :=
  c.1 = d.1 ∨ c.2 = d.2 ∨ (c.1.val / 3 = d.1.val / 3 ∧ c.2.val / 3 = d.2.val / 3)

/-- A filled grid `g` (assigning one of nine digits to every cell) is a solved Sudoku grid if
no two distinct cells that see each other hold the same digit. Equivalently, every row, every
column and every $3 \times 3$ box contains each of the nine digits exactly once. -/
def IsSudokuGrid (g : Cell → Fin 9) : Prop :=
  ∀ c d, c ≠ d → Sees c d → g c ≠ g d

/-- A Sudoku puzzle is a partially filled grid: `p c = some k` means that the cell `c` is a
given holding the digit `k`, and `p c = none` means that the cell `c` is empty. -/
abbrev Puzzle := Cell → Option (Fin 9)

/-- The number of givens (clues) of a puzzle, i.e. the number of filled cells. -/
def Puzzle.numGivens (p : Puzzle) : ℕ :=
  (Finset.univ.filter fun c => (p c).isSome).card

/-- A filled grid `g` is a solution of the puzzle `p` if it is a solved Sudoku grid which agrees
with every given of `p`. -/
def Puzzle.IsSolution (p : Puzzle) (g : Cell → Fin 9) : Prop :=
  IsSudokuGrid g ∧ ∀ c k, p c = some k → g c = k

/-- A puzzle is *proper* if it has exactly one solution. -/
def Puzzle.IsProper (p : Puzzle) : Prop :=
  ∃! g, p.IsSolution g

/-- The puzzle obtained from `p` by removing the given in the cell `c`, that is, by emptying
the cell `c`. -/
def Puzzle.erase (p : Puzzle) (c : Cell) : Puzzle :=
  Function.update p c none

/-- A puzzle is *minimal* if it is proper and removing any single given leaves a puzzle which
is no longer proper (that is, which has more than one solution). -/
def Puzzle.IsMinimal (p : Puzzle) : Prop :=
  p.IsProper ∧ ∀ c, (p c).isSome → ¬ (p.erase c).IsProper

/-- A puzzle has at most $81$ givens. -/
@[category API, AMS 5]
theorem Puzzle.numGivens_le (p : Puzzle) : p.numGivens ≤ 81 :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- A solution of a puzzle is still a solution after removing a given. -/
@[category API, AMS 5]
theorem Puzzle.IsSolution.erase {p : Puzzle} {g : Cell → Fin 9} (h : p.IsSolution g) (c : Cell) :
    (p.erase c).IsSolution g := by
  refine ⟨h.1, fun d k hd => h.2 d k ?_⟩
  by_cases hdc : d = c
  · subst hdc
    simp [Puzzle.erase] at hd
  · rwa [Puzzle.erase, Function.update_of_ne hdc] at hd

/-- Removing a given from a proper puzzle can only introduce additional solutions, so a puzzle
is minimal if and only if it is proper and removing any single given yields a puzzle with at
least two solutions. -/
@[category API, AMS 5]
theorem Puzzle.isMinimal_iff (p : Puzzle) :
    p.IsMinimal ↔ p.IsProper ∧ ∀ c, (p c).isSome →
      ∃ g g', g ≠ g' ∧ (p.erase c).IsSolution g ∧ (p.erase c).IsSolution g' := by
  refine and_congr_right fun hp => forall_congr' fun c => imp_congr_right fun _ => ?_
  obtain ⟨g, hg, -⟩ := hp
  constructor
  · intro hne
    by_contra hcon
    push_neg at hcon
    exact hne ⟨g, hg.erase c, fun g' hg' => by_contra fun h => hcon g' g h hg' (hg.erase c)⟩
  · rintro ⟨g₁, g₂, hne, h₁, h₂⟩ ⟨g', _, hu'⟩
    exact hne ((hu' g₁ h₁).trans (hu' g₂ h₂).symm)

/-- The puzzle whose givens are all $81$ cells of a solved Sudoku grid `g` is proper. -/
@[category API, AMS 5]
theorem Puzzle.isProper_some {g : Cell → Fin 9} (hg : IsSudokuGrid g) :
    Puzzle.IsProper (fun c => some (g c)) :=
  ⟨g, ⟨hg, fun _ _ h => Option.some_injective _ h⟩,
    fun _ h => funext fun c => h.2 c (g c) rfl⟩

/-- The grid whose cell in row $i$ and column $j$ holds the digit $3i + \lfloor i/3 \rfloor + j$
reduced modulo $9$. -/
def canonicalGrid (c : Cell) : Fin 9 :=
  ⟨(3 * c.1.val + c.1.val / 3 + c.2.val) % 9, Nat.mod_lt _ (by norm_num)⟩

/-- The canonical grid is a solved Sudoku grid. -/
@[category test, AMS 5]
theorem isSudokuGrid_canonicalGrid : IsSudokuGrid canonicalGrid := by
  rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ hne hsees heq
  simp only [canonicalGrid, Fin.mk.injEq, Sees, Prod.mk.injEq, ne_eq, not_and_or]
    at hne hsees heq
  interval_cases i <;> interval_cases i' <;> omega

/-- The empty puzzle has more than one solution, hence is not proper. -/
@[category test, AMS 5]
theorem not_isProper_empty : ¬ Puzzle.IsProper (fun _ => none) := by
  rintro ⟨g, -, hu⟩
  have h₁ := hu canonicalGrid ⟨isSudokuGrid_canonicalGrid, by simp⟩
  have h₂ := hu (fun c => canonicalGrid c + 1)
    ⟨fun c d hcd hs h => isSudokuGrid_canonicalGrid c d hcd hs (add_right_cancel h), by simp⟩
  have := congrFun (h₁.trans h₂.symm) (0, 0)
  simp at this

/--
**Maximum number of givens.** What is the maximum number of givens for a minimal puzzle?

Here a *puzzle* is a partially filled classic $9 \times 9$ Sudoku grid (with $3 \times 3$
boxes), a puzzle is *proper* if it has exactly one solution, and it is *minimal* if it is
proper and removing any one of its givens introduces additional solutions. The question asks
for the greatest element of the set of numbers of givens of minimal puzzles. This set is
nonempty (minimal puzzles exist) and bounded by $81$, so it has a greatest element. The largest
minimal puzzle found so far has $40$ givens, and $40$ is believed to be the maximum.
-/
@[category research open, AMS 5]
theorem maximum_number_of_givens :
    IsGreatest {n | ∃ p : Puzzle, p.IsMinimal ∧ p.numGivens = n} answer(sorry) := by
  sorry

end MaximumNumberOfGivens
