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
# Multiplicative order of 2 mod $2n+1$

The multiplicative order of 2 modulo $2n+1$.
In other words, the least $m > 0$ such that $2n+1$ divides $2^m - 1$.

*References:*
- [A002326](https://oeis.org/A002326)-/

namespace OeisA2326

/-- The multiplicative order of 2 modulo $2n+1$. -/
noncomputable def a (n : ℕ) : ℕ :=
  orderOf (2 : ZMod (2 * n + 1))

/--
If $p$ is an odd prime then $a((p^3-1)/2) = p \cdot a((p^2-1)/2)$.
Because otherwise $a((p^3-1)/2) < p \cdot a((p^2-1)/2)$ iff $a((p^3-1)/2) = a((p-1)/2)$
for a prime $p$. Equivalently $p^3$ divides $2^{p-1}-1$, but no such prime $p$ is known.
- Thomas Ordowski, Feb 10 2014
-/
theorem conjecture1 (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) :
    a ((p ^ 3 - 1) / 2) = p * a ((p ^ 2 - 1) / 2) := by
  sorry

end OeisA2326

theorem OeisA2326.conjecture1.disproof : ¬ (type_of% @OeisA2326.conjecture1) := sorry
