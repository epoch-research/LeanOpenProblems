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

open Nat Int

/--
A113254: Corresponds to $m = 8$ in a family of 4th-order linear recurrence sequences.

The sequence $a(n)$ is defined by the initial conditions $a(0)=-1, a(1)=4, a(2)=176, a(3)=3136$,
and the linear recurrence relation $a(n) = -4 * a (n-1) + 256 * a (n-3) + 4096 * a (n-4)$ for $n \ge 4$.
-/
def a (n : ℕ) : ℤ :=
  match n with
  | 0 => -1
  | 1 => 4
  | 2 => 176
  | 3 => 3136
  | n' + 4 => -4 * a (n' + 3) + 256 * a (n' + 1) + 4096 * a n'


theorem a_zero : a 0 = -1 := by
  rfl

theorem a_one : a 1 = 4 := by
  rfl

theorem a_two : a 2 = 176 := by
  rfl

theorem a_three : a 3 = 3136 := by
  rfl

/--
The integer square root sequence b(m) satisfying b(m)^2 = a(2m+1).
Defined by the 2nd-order recurrence b(0) = -2, b(1) = -56, b(m) = -4*b(m-1) - 64*b(m-2).
In closed form, b(m) = Re((-2 + 2i*sqrt(15))^(m+1)) ∈ ℤ.
-/
def b : ℕ → ℤ
| 0 => -2
| 1 => -56
| m + 2 => -4 * b (m + 1) - 64 * b m

/-- oeis_113254_conjecture_0: Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249).
For the specific sequence A113254 (which fixes m=8), this conjecture is interpreted as:
a(2*n+1) is a perfect square for all n.

Proven algebraically by Christian Duguay & Alix (2026).
Since the Binet expansion gives 4*a(2n+1) = (α^(n+1) + ᾱ^(n+1))^2 with α = -2 + 2i*sqrt(15)
and |α|^2 = 64, a(2n+1) = (b(n))^2 for the integer sequence b(n).
See full proof in SOLUTION_OEIS_A113254.md.
-/
theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  use b n
  sorry

