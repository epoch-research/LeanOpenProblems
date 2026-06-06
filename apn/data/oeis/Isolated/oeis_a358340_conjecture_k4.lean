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

open Nat List Set

/-- A number is zeroless if its decimal digits are all non-zero. -/
def is_zeroless (k : ℕ) : Prop := 0 ∉ Nat.digits 10 k

/-- Predicate for $m$ to be an $n$-digit number. Assumes $n \ge 1$. -/
def is_n_digit (m n : ℕ) : Prop := 10^(n-1) ≤ m ∧ m < 10^n

/--
A358340: $a(n)$ is the smallest $n$-digit number whose fourth power is zeroless.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  -- Define the set S of numbers satisfying the properties.
  let S : Set ℕ := { m : ℕ | is_n_digit m n ∧ is_zeroless (m ^ 4) }
  -- sInf returns the minimum element of the set S.
  sInf S

/--
A358340 It has been proved that there exist infinitely many zeroless squares and cubes but there is apparently no proof for 4th powers, 5th powers, etc.

Formalized as the conjecture that the set of natural numbers whose fourth power is zeroless is infinite.
This is equivalent to the statement that the set $\{ m : ℕ \mid \text{is\_n\_digit}(m, n) \land \text{is\_zeroless}(m^4) \}$ is non-empty for all $n \ge 1$, ensuring $a(n)$ is defined for all $n$.
-/
theorem oeis_a358340_conjecture_k4 : Set.Infinite { m : ℕ | is_zeroless (m ^ 4) } := by
  sorry
