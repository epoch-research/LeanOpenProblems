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
# Digital sum of the Fermat number $2^{2^n} + 1$

`a n` is the digital sum of the Fermat number $2^{2^n} + 1$.
The conjecture asks if there are any prime numbers in this sequence beyond $n=11$.

*References:*
- [A108301](https://oeis.org/A108301)
-/

namespace OeisA108301

/-- The primary defining sequence `a`.
`a n` is the digital sum of the Fermat number $2^{2^n} + 1$. -/
def a (n : ℕ) : ℕ :=
  (Nat.digits 10 (2 ^ 2 ^ n + 1)).sum

/-- $a(0)$, $a(1)$, $a(5)$, $a(6)$, $a(7)$ and $a(11)$ are primes. Are there any more? -/
theorem conjecture : ∃ n > 11, (a n).Prime := by
  sorry

end OeisA108301

theorem OeisA108301.conjecture.disproof : ¬ (type_of% @OeisA108301.conjecture) := sorry
