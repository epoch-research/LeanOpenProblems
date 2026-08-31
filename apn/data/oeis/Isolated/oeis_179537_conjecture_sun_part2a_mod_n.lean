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

open Finset Nat Int

/--
A179537: The sequence
$$a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n-k}{k}^2 (-16)^k$$
-/
def A179537 (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    ((choose n k : ℤ) ^ 2) * ((choose (n - k) k : ℤ) ^ 2) * ((-16 : ℤ) ^ k)

/-- The sum $\sum_{k=0}^{p-1} (-1)^k \cdot \text{A179537}(k)$ -/
def A179537_sum_unweighted (p : ℕ) : ℤ :=
  (Finset.range p).sum fun k : ℕ => ((-1 : ℤ) ^ k) * (A179537 k)

-- Definition of the auxiliary sum for the latter parts of Sun's conjecture
def A179537_sum_weighted (n : ℕ) : ℤ :=
  (Finset.range n).sum fun k : ℕ =>
    (((42 : ℤ) * Int.ofNat k + (37 : ℤ)) * ((-1 : ℤ) ^ k) * (A179537 k))

-- Legendre symbol $\left(\frac{\cdot}{7}\right)$
noncomputable def leg_sym_7 (p : ℕ) [h_prime : Fact p.Prime] : ℤ :=
  legendreSym p 7

/--
OEIS A179537 Conjecture 0 (Zhi-Wei Sun). Part 2a: Modulo $n$ congruence for the weighted sum.
$$ \sum_{k=0}^{n-1}(42k+37)(-1)^k a(k) \equiv 0 \pmod n $$
for all $n \ge 1$.
-/
theorem oeis_179537_conjecture_sun_part2a_mod_n :
  ∀ n : ℕ, n ≥ 1 → A179537_sum_weighted n ≡ 0 [ZMOD n] := by sorry

theorem oeis_179537_conjecture_sun_part2a_mod_n.disproof : ¬ (type_of% @oeis_179537_conjecture_sun_part2a_mod_n) := sorry
