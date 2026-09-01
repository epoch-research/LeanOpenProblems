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
# Denominators of coefficients in Stirling's expansion for $\log(\Gamma(z))$

The $n$-th term is the denominator of $\frac{B_{2n}}{2n(2n-1)}$ where $B_{2n}$ is the $2n$-th
Bernoulli number.

*References:*
- [A046969](https://oeis.org/A046969)-/

namespace OeisA46969

/-- Denominators of coefficients in Stirling's expansion for $\log(\Gamma(z))$. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let m := 2 * n
    let k := m * (m - 1)
    (bernoulli m / (k : ℚ)).den

/-- $A005382(n)$ is the $n$-th prime $p$ such that $2p-1$ is also prime (1-based). -/
noncomputable def a005382 (n : ℕ) : ℕ :=
  Nat.nth (fun p ↦ p.Prime ∧ (2 * p - 1).Prime) (n - 1)

/--
Conjecture II: if $\frac{a(n)}{12}$ is prime, then $\frac{a(n-1)}{12} - (n-1)$,
$\frac{a(n)}{12} - n$ and $\frac{a(n+2)}{12} - (n+2)$ are multiples of 6.
- Lorenzo Sauras Altuzarra, Oct 13 2020
-/
theorem conjecture2 (n : ℕ) (hn : 2 ≤ n)
    (h_div : 12 ∣ a n) (h_prime : Nat.Prime (a n / 12))
    (h_div_prev : 12 ∣ a (n - 1)) (h_div_succ : 12 ∣ a (n + 2)) :
    6 ∣ ((a (n - 1) / 12 : ℤ) - (n - 1 : ℤ)) ∧
    6 ∣ ((a n / 12 : ℤ) - (n : ℤ)) ∧
    6 ∣ ((a (n + 2) / 12 : ℤ) - (n + 2 : ℤ)) := by
  sorry

end OeisA46969

theorem OeisA46969.conjecture2.disproof : ¬ (type_of% @OeisA46969.conjecture2) := sorry
