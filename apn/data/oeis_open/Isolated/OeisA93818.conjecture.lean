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
# $\gcd(\mathrm{numerator}(H_n), n!)$

$a(n) = \gcd(\mathrm{A001008}(n), n!)$, where $\mathrm{A001008}(n)$ is the numerator of
the $n$-th harmonic number $H_n = \sum_{i=1}^n \frac{1}{i}$.

*References:*
- [A093818](https://oeis.org/A093818)-/

namespace OeisA93818

/-- $a(n) = \gcd(\mathrm{numerator}(H_n), n!)$, where $H_n$ is the $n$-th harmonic number. -/
def a (n : ℕ) : ℕ :=
  Nat.gcd (harmonic n).num.natAbs n.factorial

/--
Conjecture: Every odd prime occurs as a term in the sequence.-/
theorem conjecture (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) : ∃ n > 0, a n = p := by
  sorry

end OeisA93818

theorem OeisA93818.conjecture.disproof : ¬ (type_of% @OeisA93818.conjecture) := sorry
