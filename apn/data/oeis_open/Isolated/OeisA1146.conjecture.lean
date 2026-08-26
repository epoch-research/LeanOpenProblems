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
# $a(n) = 2^(2^n)$

*References:*
- [A001146](https://oeis.org/A001146)
-/

namespace OeisA1146

/--
The primary defining sequence `a`.
$a(n) = 2^{2^n}$.
-/
def a (n : ℕ) : ℕ := 2 ^ (2 ^ n)

/--
I conjecture that { $a(n)$ ; $n>1$ } are the numbers such that $n^4-1$ divides $2^n-1$,
intersection of A247219 and A247165. - M. F. Hasler, Jul 25 2015
This formalizes the reverse direction.
-/
theorem conjecture :
  ∀ k : ℕ, ((k^4 - 1) : ℕ) ∣ (2^k - 1 : ℕ) → k > 1 → ∃ n : ℕ, 2 ≤ n ∧ k = a n := by
  sorry

end OeisA1146
