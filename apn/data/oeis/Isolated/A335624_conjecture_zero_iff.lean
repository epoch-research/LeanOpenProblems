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

open Nat Finset

/--
A335624: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x + 3y + 4z$ a square,
where $x, y, z, w$ are nonnegative integers.
-/
def A335624 (n : ℕ) : ℕ :=
  -- The variables x, y, z, w are bounded by sqrt(n), since they are non-negative.
  let B : ℕ := Nat.sqrt n + 1
  let R := range B

  R.sum fun x =>
  R.sum fun y =>
  R.sum fun z =>
  R.sum fun w =>
    if x^2 + y^2 + z^2 + w^2 = n
      -- The term x + 3*y + 4*z must be a perfect square.
      ∧ (let m := x + 3 * y + 4 * z; Nat.sqrt m ^ 2 = m)
    then 1 else 0

/--
Conjecture: a(n) = 0 if and only if n has the form $2^{4k+3} \cdot m$ (k >= 0 and m = 1, 3, 5, 43).
This is the main part of the OEIS conjecture.
-/
theorem A335624_conjecture_zero_iff (n : ℕ) :
  A335624 n = 0 ↔
    ∃ (k : ℕ) (m : ℕ),
      m ∈ ({1, 3, 5, 43} : Set ℕ) ∧
      n = 2 ^ (4 * k + 3) * m :=
by sorry
