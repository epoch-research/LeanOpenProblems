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
# Odious primes minus evil primes among first $n$ primes

$a(n)$ is the number of primes with odd binary weight (odious primes) among the first $n$ primes
minus the number with even binary weight (evil primes).

*References:*
- [A130911](https://oeis.org/A130911)-/

namespace OeisA130911

/-- Parity sign of binary weight: $+1$ if popcount is odd, $-1$ if even. -/
def signWeight (k : ℕ) : ℤ :=
  if (Nat.digits 2 k).sum % 2 = 1 then 1 else -1

/-- $a(n) = \sum_{i=0}^{n-1} \mathrm{signWeight}(p_i)$ where $p_i$ is the $i$-th prime. -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, signWeight (Nat.nth Nat.Prime i)

/--
Shevelev conjectures that $a(n) \ge 0$ for $n > 3$.-/
theorem conjecture (n : ℕ) (hn : 3 < n) : a n ≥ 0 := by
  sorry

end OeisA130911
