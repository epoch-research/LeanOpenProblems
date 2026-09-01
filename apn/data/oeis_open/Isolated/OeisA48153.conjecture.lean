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
# $a(n) = \sum_{k=1}^n (k^2 \bmod n)$

*References:*
- [A048153](https://oeis.org/A048153)-/

namespace OeisA48153

/-- $a(n) = \sum_{k=1}^n (k^2 \bmod n)$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, (k ^ 2 % n)

/--
"Conjecture: $a(n) <= \frac{n^2-1}{2}$. - _Aspen A.M. Meissner_, Mar 06 2025"-/
theorem conjecture (n : ℕ) (hn : 1 ≤ n) : a n ≤ (n ^ 2 - 1) / 2 := by
  sorry

end OeisA48153

theorem OeisA48153.conjecture.disproof : ¬ (type_of% @OeisA48153.conjecture) := sorry
