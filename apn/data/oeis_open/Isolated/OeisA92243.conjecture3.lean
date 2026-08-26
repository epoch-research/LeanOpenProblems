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
# Tug of war score between prime gap increases and decreases

Score at stage $n$ in "tug of war" between prime gap increases vs. prime gap decreases:
start with score $= 0$ at $n = 1$ and at stage $k > 1$, increase (resp. decrease) the score by $1$
if the $k$-th prime gap is greater (resp. less) than the previous prime gap.

*References:*
- [A092243](https://oeis.org/A092243)-/

namespace OeisA92243

/-- The $n$-th prime gap $g(n) = p_n - p_{n-1}$ for $n \ge 1$,
where $p_i$ is the $i$-th prime (0-indexed). -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1)

/-- Score at stage $n$ in "tug of war" between prime gap increases vs. prime gap decreases. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n ≤ 1 then 0
  else
    ∑ k ∈ Finset.Icc 2 n,
      ((primeGap k : ℤ) - (primeGap (k - 1) : ℤ)).sign

/--
Is the score $a(n)$ bounded from above?-/
theorem conjecture3 : ∃ B : ℤ, ∀ n : ℕ, a n ≤ B := by
  sorry

end OeisA92243
