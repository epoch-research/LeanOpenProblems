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
# Number of primes $< n^3$

Number of primes strictly less than $n^3$.

*References:*
- [A038098](https://oeis.org/A038098)-/

namespace OeisA38098

/-- Number of primes strictly less than $n^3$. -/
def a (n : ℕ) : ℕ := (Nat.primesBelow (n ^ 3)).card

/--
Conjecture (i): for any integer $k > 2$, the sequence $\pi(n^k)/n^k$ ($n = 2, 3, \ldots$) is strictly
decreasing, where $\pi(x)$ denotes the number of primes not exceeding $x$.
- Zhi-Wei Sun, Oct 17 2015
-/
theorem conjecture1 (k : ℕ) (hk : 2 < k) (n : ℕ) (hn : 2 ≤ n) :
    (Nat.primeCounting ((n + 1) ^ k) : ℚ) / ((n + 1) ^ k : ℚ) <
    (Nat.primeCounting (n ^ k) : ℚ) / (n ^ k : ℚ) := by
  sorry

end OeisA38098
