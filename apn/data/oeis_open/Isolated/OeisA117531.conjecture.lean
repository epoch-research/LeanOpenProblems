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
# Number of primes in $n$-th row of triangle $k^2 - k + p_n$

$a(n)$ is the number of primes in the $n$-th row of the triangle $T(n, k) = k^2 - k + p_n$
for $1 \le k \le n$, where $p_n$ is the $n$-th prime ($p_1=2, p_2=3, \dots$).

*References:*
- [A117531](https://oeis.org/A117531)-/

namespace OeisA117531

/-- Number of primes in the $n$-th row of $T(n, k) = k^2 - k + p_n$ for $1 \le k \le n$. -/
noncomputable def a (n : ℕ) : ℕ :=
  let pn : ℕ := Nat.nth Nat.Prime (n - 1)
  Finset.card ((Finset.Icc 1 n).filter fun k => (k ^ 2 - k + pn).Prime)

/--
Conjecture: $a(n) < n$ for $n > 13$.-/
theorem conjecture (n : ℕ) (h : n > 13) : a n < n := by
  sorry

end OeisA117531
