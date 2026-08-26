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
# Smallest $m$ such that $n^3 + m^3 + 1$ is prime

$a(n)$ is the smallest natural number $m \ge 1$ such that $n^3 + m^3 + 1$ is prime.

*References:*
- [A159829](https://oeis.org/A159829)-/

namespace OeisA159829

open Classical in
/-- $a(n)$ is the smallest natural number $m \ge 1$ such that $n^3 + m^3 + 1$ is prime,
or `none` if no such $m$ exists. -/
noncomputable def a (n : ℕ) : Option ℕ :=
  if ∃ m : ℕ, 1 ≤ m ∧ (n ^ 3 + m ^ 3 + 1).Prime then
    some (sInf {m : ℕ | 1 ≤ m ∧ (n ^ 3 + m ^ 3 + 1).Prime})
  else
    none

/--
Conjecture 2: For any $k \ge 3$, there are infinitely many primes of the form $n^k + m^k + 1$
for $n, m \ge 1$.
- _Ulrich Krug_, 2009
-/
theorem conjecture2 (k : ℕ) (hk : 3 ≤ k) :
    Set.Infinite {p : ℕ | ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ p.Prime ∧ p = n ^ k + m ^ k + 1} := by
  sorry

end OeisA159829
