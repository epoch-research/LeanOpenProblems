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
The sequence A218656: Number of ways to write $2n+1$ as $x+y$ with $0 < x < y$ and $x^4 + y^4$ prime.
This is equivalent to the number of $k \in \{1, \dots, n\}$ such that $k^4 + (2n+1-k)^4$ is prime.
-/
def a (n : ℕ) : ℕ :=
  card ((Icc 1 n).filter fun k : ℕ => Nat.Prime (k ^ 4 + (2 * n + 1 - k) ^ 4))

-- Note: These theorems provided in the context are intentionally kept unchanged.
/--
Auxiliary theorem formalizing the empirical claim about the verification range
for the $x^4 + y^4$ case.
The claim: "no exceptions for x^4 + y^4" for $2n+1 \le 10^6$.
This is equivalent to $a(n) > 0$ for $1 \le n \le (10^6-1)/2 = 499999$.
Note: $500000 = 10^6/2$. If $2n+1 \le 10^6$, then $2n \le 999999$, so $n \le 499999$.
-/
theorem oeis_A218656_verified_range (n : ℕ) (hval : n ≤ 499999) (hn : 0 < n) : a n > 0 :=
  sorry
