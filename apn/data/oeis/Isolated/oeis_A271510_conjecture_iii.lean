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

import FormalConjectures.Util.ProblemImports

open Nat

/--
A271510: Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x \ge y \ge 0$, $z \ge 0$ and $w \ge 0$ such that $x^2 + 8y^2 + 16z^2$ is a square.
-/
def A271510 (n : ℕ) : ℕ :=
  -- Define the decidable predicate for being a perfect square in ℕ.
  let is_square (k : ℕ) : Prop := k.sqrt * k.sqrt = k

  -- The maximum value for any variable is $\lfloor\sqrt{n}\rfloor$.
  let bound := n.sqrt
  let R : Finset ℕ := Finset.range (bound + 1)

  -- The search space is the Cartesian product R x R x R x R, structured as (((ℕ × ℕ) × ℕ) × ℕ).
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) := R.product R |>.product R |>.product R

  Finset.card $ search_space.filter fun p =>
    -- Decompose the nested product tuple p = (((x, y), z), w)
    let x := p.fst.fst.fst
    let y := p.fst.fst.snd
    let z := p.fst.snd
    let w := p.snd

    -- Constraint 1: sum of squares equals n
    x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
    -- Constraint 2: $x \ge y$
    x ≥ y ∧
    -- Constraint 3: $x^2 + 8y^2 + 16z^2$ is a square.
    is_square (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2)

-- A standard definition for "is a square" on ℕ
def is_square (k : ℕ) : Prop := ∃ m : ℕ, k = m^2

/--
Conjecture (iii) from OEIS A271510:
For any ordered pair (b, c) = (48, 112), (63, 7), (112, 1008), (136, 24), (136, 216), (360, 40), (840, 280), (1008, 112), each natural number can be written as x^2 + y^2 + z^2 + w^2 with x >= y >= 0, z >=0 and w >= 0 such that 9*x^2 + b*y^2 + c*z^2 is a square.
-/
theorem oeis_A271510_conjecture_iii (b c : ℕ) :
  (b = 48 ∧ c = 112) ∨
  (b = 63 ∧ c = 7) ∨
  (b = 112 ∧ c = 1008) ∨
  (b = 136 ∧ c = 24) ∨
  (b = 136 ∧ c = 216) ∨
  (b = 360 ∧ c = 40) ∨
  (b = 840 ∧ c = 280) ∨
  (b = 1008 ∧ c = 112) →
  ∀ n : ℕ, ∃ x y z w : ℕ,
    x^2 + y^2 + z^2 + w^2 = n ∧
    x ≥ y ∧
    is_square (9*x^2 + b*y^2 + c*z^2)
  := by sorry
