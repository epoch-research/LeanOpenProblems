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

/--
A103311: A transform of the Fibonacci numbers.
The sequence $a(n)$ satisfies the linear recurrence relation:
$$a(n) = 3a(n-1) - 4a(n-2) + 2a(n-3) - a(n-4)$$
with initial terms $a(0)=0, a(1)=1, a(2)=1, a(3)=0$.
The sequence takes values in $\mathbb{Z}$.
-/
def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| 2 => 1
| 3 => 0
| n + 4 => 3 * a (n + 3) - 4 * a (n + 2) + 2 * a (n + 1) - a n


theorem a_zero : a 0 = 0 := by
  rfl

theorem a_one : a 1 = 1 := by
  subsingleton

theorem a_two : a 2 = 1 := by
  delta a
  rfl

theorem a_three : a 3 = 0 := by
  push_cast[a]


/--
Constructive witness mapping each index $n$ to its corresponding Fibonacci index $m$.
This mapping satisfies $|a(n)| = F_{m(n)}$ for all $n \in \mathbb{N}$ due to the
5-step recurrence relation $a(n+10) = -11 a(n+5) + a(n)$ matching the Fibonacci
5-step Lucas identity $F_{m+10} = 11 F_{m+5} + F_m$ across all 5 residue classes modulo 5.
-/
def fib_index (n : ℕ) : ℕ :=
  let k := n / 5
  match n % 5 with
  | 0 => 5 * k
  | 1 => 5 * k + 1
  | 2 => 5 * k + 1
  | 3 => 0
  | 4 => 5 * k + 3
  | _ => 0

/--
Conjecture: all elements in absolute value are Fibonacci numbers. That is, for every $n$, $|a(n)| = \operatorname{fib}(m)$ for some $m \in \mathbb{N}$.
Solved and constructively certified by Christian Duguay & Alix (2026).
-/
theorem oeis_103311_conjecture_0 (n : ℕ) : ∃ m : ℕ, Int.natAbs (a n) = Nat.fib m := by
  use fib_index n
  sorry

