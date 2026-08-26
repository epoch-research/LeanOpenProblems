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
# Chua's Euclidean prime sequence

For a product $n$ of the preceding terms, Chua's sequence chooses the least
prime dividing $d + n / d$ for some divisor $d$ of $n$. The open question is
whether every prime occurs.

*References:*
- [OEIS A167604](https://oeis.org/A167604)
- Andrew R. Booker,
  [A variant of the Euclid--Mullin sequence containing every prime](https://arxiv.org/abs/1605.08929)
-/

namespace OeisA167604

/-- The least prime occurring among the sums $d + n / d$ for divisors $d$ of $n$.

Taking the least prime factor of the product gives the same minimum and makes the definition
directly executable. -/
def next (n : ℕ) : ℕ :=
  Nat.minFac (∏ d ∈ n.divisors, (d + n / d))

/-- Product of the first $n$ terms of Chua's sequence. -/
def product : ℕ → ℕ
  | 0 => 1
  | n + 1 => product n * next (product n)

/-- Chua's sequence, extended by $a(0) = 1$. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => next (product n)

/-- Does Chua's sequence contain every prime? -/
theorem conjecture :
    ∀ p : ℕ, p.Prime → ∃ n ≥ 1, a n = p := by
  sorry

end OeisA167604
