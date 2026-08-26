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
# $a(n) = (\text{smallest prime} > n^2) - n^2$

The difference between the smallest prime strictly greater than $n^2$ and $n^2$.

*References:*
- [A053000](https://oeis.org/A053000)-/

namespace OeisA53000

/-- $a(n) = (\text{smallest prime} > n^2) - n^2$. -/
noncomputable def a (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ n ^ 2 < p}) - n ^ 2

/--
Conjecture: $a(n) \le 1 + \phi(n)$ for $n > 0$. This improves on Oppermann's conjecture, which says
$a(n) < n$.
- Thomas Ordowski, Dec 17 2014
-/
theorem conjecture (n : ℕ) (hn : 0 < n) : a n ≤ 1 + n.totient := by
  sorry

end OeisA53000
