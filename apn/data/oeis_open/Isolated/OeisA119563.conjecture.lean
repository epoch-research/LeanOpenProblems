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
# Sum of Fermat number and Mersenne number minus 1: $2^{2^n} + 2^n - 1$

Define $F(n) = 2^{2^n} + 1$ (the $n$-th Fermat number) and $M(n) = 2^n - 1$ (the $n$-th Mersenne
number). Then $a(n) = F(n) + M(n) - 1 = 2^{2^n} + 2^n - 1$.

*References:*
- [A119563](https://oeis.org/A119563)-/

namespace OeisA119563

/-- $a(n) = 2^{2^n} + 2^n - 1$. -/
def a (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 2 ^ n - 1

/--
The first 5 entries are primes. Are there infinitely many primes in this sequence?-/
theorem conjecture : Set.Infinite {n : ℕ | (a n).Prime} := by
  sorry

end OeisA119563
