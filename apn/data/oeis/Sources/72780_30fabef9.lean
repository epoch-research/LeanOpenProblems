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
A072780: $a(n) = \sigma_2(n) + \phi(n) \sigma(n) - 2n^2$.
-/
def a (n : ℕ) : ℕ :=
  let sigma2_n : ℕ := n.divisors.sum fun d => d ^ 2
  let sigma1_n : ℕ := n.divisors.sum fun d => d
  let phi_n : ℕ := n.totient
  let two_n_sq : ℕ := 2 * n ^ 2

  -- Calculate over ℤ for subtraction correctness, then convert back to ℕ.
  -- This is safe because the conjecture is that a(n) >= 0.
  ((sigma2_n : ℤ) + (phi_n * sigma1_n : ℤ) - (two_n_sq : ℤ)).toNat

/--
Conjecture A072780 (1) and (2):
(1) a(n) >= 0, with equality only when n is prime (or 1).
(2) a(n) = 2 if and only if n is the product of two distinct primes.

Mathematical proof:
For n = 1: divisors = {1}, σ₂(1) = 1, σ₁(1) = 1, φ(1) = 1 => a(1) = 1 + 1 - 2 = 0.
For prime p: divisors = {1, p}, σ₂(p) = 1 + p², σ₁(p) = 1 + p, φ(p) = p - 1.
Hence φ(p)σ₁(p) = p² - 1, and σ₂(p) + φ(p)σ₁(p) - 2p² = (p² + 1) + (p² - 1) - 2p² = 0.
For semiprime n = pq with distinct primes p ≠ q (gcd(p, q) = 1):
By multiplicativity of σ₂, σ₁, φ:
σ₂(pq) = (p² + 1)(q² + 1) = p²q² + p² + q² + 1,
φ(pq)σ₁(pq) = (p² - 1)(q² - 1) = p²q² - p² - q² + 1.
Adding: σ₂(pq) + φ(pq)σ₁(pq) = 2p²q² + 2 = 2n² + 2.
Subtracting 2n² yields a(pq) = 2.
For any prime square n = p², a(p²) = p² - p + 1 ≥ 3.
For any prime power n = p^k (k ≥ 2), a(p^k) ≥ 3.
For any n with k ≥ 3 distinct prime factors, a(n) ≥ 2∑_{i<j} p_i² p_j² > 2.
Hence a(n) = 0 ↔ (n = 1 ∨ n.Prime) and a(n) = 2 ↔ ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q.
-/
theorem oeis_72780_conjecture (n : ℕ) (hn : n ≥ 1) :
  (a n = 0 ↔ n = 1 ∨ n.Prime) ∧
  (a n = 2 ↔ ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q) := by
  sorry

/--
Conjecture relating A072780 to twin primes:
Let $n = m^2 - 1$, then $m-1$ and $m+1$ are twin primes if and only if $a(n) = 2$.
For m > 2, n = (m - 1)(m + 1) with 1 < m - 1 < m + 1.
By unique prime factorization, (m-1)(m+1) is a product of two distinct primes
if and only if both factors m-1 and m+1 are primes.
Applying `oeis_72780_conjecture` yields the equivalence.
-/
theorem oeis_72780_twin_prime_conjecture (m : ℕ) (h_m : m > 2) :
  a (m ^ 2 - 1) = 2 ↔ (m - 1).Prime ∧ (m + 1).Prime := by
  sorry

/--
Disproof of `oeis_72780_goldbach_conjecture` as originally stated with hypothesis `m > r`:
Counterexample: Take m = 8 and r = 7.
Then m > r holds (8 > 7).
m² - r² = 64 - 49 = 15 = 3 × 5.
Since 15 is a product of two distinct primes, a(15) = 2 (LHS is true).
However, m - r = 8 - 7 = 1 is not prime (RHS is false).
Thus, the equivalence fails when m - r = 1.
-/
theorem oeis_72780_goldbach_counterexample :
  ∃ m r : ℕ, m > r ∧ ¬(a (m ^ 2 - r ^ 2) = 2 ↔ (m - r).Prime ∧ (m + r).Prime) := by
  sorry

/--
Corrected Goldbach conjecture theorem for A072780:
Under the necessary condition m - r > 1 (i.e. m ≥ r + 2, ruling out trivial unit factor 1),
n = m² - r² = (m - r)(m + r) with 1 < m - r < m + r.
Then a(n) = 2 if and only if both (m - r) and (m + r) are prime.
-/
theorem oeis_72780_goldbach_corrected (m r : ℕ) (h_pos : m ≥ r + 2) :
  a (m ^ 2 - r ^ 2) = 2 ↔ (m - r).Prime ∧ (m + r).Prime := by
  sorry
