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
# Recurrence $a(n) = (a(n-1) + a(n-2)) \pmod n$

$a(0) = a(1) = 1$; $a(n) = (a(n-1) + a(n-2)) \pmod n$.

*References:*
- [A096535](https://oeis.org/A096535)-/

namespace OeisA96535

/-- Recurrence $a(n) = (a(n-1) + a(n-2)) \pmod n$. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => (a (n + 1) + a n) % (n + 2)

/--
All numbers appear infinitely often, i.e., for every number $k \ge 0$ and every frequency $f > 0$
there is an index $i$ such that $a(i) = k$ is the $f$-th occurrence of $k$ in the sequence.
- _Klaus Brockhaus_, Aug 29 2006
-/
theorem conjecture (k : ℕ) (N : ℕ) : ∃ i : ℕ, i > N ∧ a i = k := by
  sorry

end OeisA96535
