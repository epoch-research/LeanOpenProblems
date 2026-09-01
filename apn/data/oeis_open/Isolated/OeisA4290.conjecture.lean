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
# Least positive multiple of $n$ in base 10 with digits 0 and 1

Least positive multiple of $n$ that when written in base 10 uses only 0's and 1's.

*References:*
- [A004290](https://oeis.org/A004290)
-/

namespace OeisA4290

/-- Least positive multiple of $n$ using only 0's and 1's in base 10. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }

/--
It is known that $a(10^k - 1) = (10^{9k} - 1) / 9$ for all $k$.
Is $a(n) < a(10^k - 1)$ for all $n < 10^k - 1$?
- David Radcliffe, Aug 01 2025
-/
theorem conjecture (k : ℕ) :
    ∀ n < 10 ^ k - 1, a n < a (10 ^ k - 1) := by
  sorry

end OeisA4290

theorem OeisA4290.conjecture.disproof : ¬ (type_of% @OeisA4290.conjecture) := sorry
