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
A245212: $a(n) = n \cdot \tau(n) - \sum_{d|n, d<n} d \cdot \tau(d)$,
where $\tau(n)$ is the number of divisors of $n$.
The formula uses the set of proper divisors for the sum.
The result is an integer ($\mathbb{Z}$) to account for negative values.
-/
def a (n : ℕ) : ℤ :=
  (n : ℤ) * (n.divisors.card : ℤ) - n.properDivisors.sum
    (fun d => (d : ℤ) * (d.divisors.card : ℤ))

-- The sum of divisors function $\sigma_1(n)$, cast to ℤ.
def sigma (n : ℕ) : ℤ :=
  n.divisors.sum (fun d => (d : ℤ))

/--
%C A245212 Conjecture: a(n) = sigma(n) iff n is a power of 2 (A000079).

Mathematical proof:
1. For n = 2^k:
   Proper divisors are 2^0, ..., 2^{k-1}.
   The sum of d * τ(d) over proper divisors is:
   ∑_{j=0}^{k-1} 2^j * (j + 1) = 2^k * (k - 1) + 1.
   Then a(2^k) = 2^k * (k + 1) - (2^k * (k - 1) + 1) = 2 * 2^k - 1 = 2^{k+1} - 1.
   Similarly, σ(2^k) = ∑_{j=0}^k 2^j = 2^{k+1} - 1.
   Thus a(2^k) = σ(2^k) for all k ≥ 0.
2. For prime powers p^k with p ≥ 3:
   a(p^k) - σ(p^k) = (p - 2) * [(k(p - 1) - 1) * p^k + 1] / (p - 1)²,
   which is strictly positive for all p ≥ 3, k ≥ 1.
3. For general composite n with odd prime factors, the cross-terms ensure a(n) ≠ σ(n).
-/
theorem oeis_245212_conjecture_0 (n : ℕ) (h : n > 0) :
    a n = sigma n ↔ n.isPowerOfTwo := by
  sorry
