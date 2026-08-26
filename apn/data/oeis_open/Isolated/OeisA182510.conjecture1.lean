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
# Recurrence with bitwise XOR

The sequence is defined by $a(0) = 0$, $a(1) = 1$, and for $n \ge 0$,
$$a(n+2) = (a(n+1) \mathbin{\mathrm{XOR}} (n+2)) - a(n),$$
where $\mathrm{XOR}$ is the bitwise exclusive-or operator on integers.

*References:*
- [A182510](https://oeis.org/A182510)-/

namespace OeisA182510

/-- Defining recurrence for $a(n)$. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => Int.xor (a (n + 1)) (n + 2 : ℤ) - a n

/--
Conjecture: the sequence contains 8 zeros.-/
theorem conjecture1 : Set.ncard {n : ℕ | a n = 0} = 8 := by
  sorry

end OeisA182510
