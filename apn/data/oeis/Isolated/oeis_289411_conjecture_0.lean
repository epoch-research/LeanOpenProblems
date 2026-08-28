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
open scoped BigOperators

/--
A289411: $\mathrm{a}(n) = \sum_{k=0}^n \mathrm{sign}(\mathrm{A007953}(5k) - \mathrm{A007953}(k))$.
$\mathrm{A007953}(n)$ is the digital sum of $n$ in base 10.
The sequence is non-negative, so the sum over $\mathbb{Z}$ is converted to $\mathbb{N}$.
-/
def A289411 (n : ℕ) : ℕ :=
  let digital_sum_ten (m : ℕ) : ℕ := (Nat.digits 10 m).sum
  (Finset.range (n + 1)).sum (fun k =>
    Int.sign ((digital_sum_ten (5 * k) : ℤ) - (digital_sum_ten k : ℤ)))
  |>.toNat

/--
this relation is conjectured to hold for any k > 0, where $m_k = 10^k/2 - 1$.
The relation is $a(m_k - i) = a(m_k + i)$ for $i = 0 \dots m_k$.
-/
theorem oeis_289411_conjecture_0 (k : ℕ) (hk : 0 < k) :
  let m_k : ℕ := (10 ^ k) / 2 - 1
  ∀ i : ℕ, i ≤ m_k → A289411 (m_k - i) = A289411 (m_k + i) :=
by sorry

theorem oeis_289411_conjecture_0.disproof : ¬ (type_of% @oeis_289411_conjecture_0) := sorry
