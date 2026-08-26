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
# Smallest index $k > n$ such that $(p_k+p_{k+1})/(p_n+p_{n+1})$ is an integer $\ge 2$

*References:*
- [A167918](https://oeis.org/A167918)-/

namespace OeisA167918

/-- $P(i)$ is the $i$-th prime, 1-indexed. -/
noncomputable def P (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- $S(i) = p_i + p_{i+1}$. -/
noncomputable def S (i : ℕ) : ℕ := P i + P (i + 1)

/-- Smallest index $k > n$ such that $S(n) \mid S(k)$. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else sInf { k : ℕ | k > n ∧ S n ∣ S k }

/--
Conjecture: $f(n, k) = 2$ for infinitely many cases, where $k = a(n)$.

We assume $a(n) \ne 0$ (i.e., that a suitable $k > n$ always exists), as `sInf` evaluates to $0$
on an empty set.
-/
theorem conjecture1 (M : ℕ) (ha : ∀ n > 0, a n ≠ 0) :
    ∃ n : ℕ, n ≥ M ∧ n > 0 ∧ S (a n) = 2 * S n := by
  sorry

end OeisA167918
