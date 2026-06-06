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

import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A248123: Least integer $m > 0$ such that $\gcd(m,n) = 1$ and $m \cdot n \mid C(m+n)$,
where $C(k)$ refers to the $k$-th Catalan number $\binom{2k}{k}/(k+1)$.
-/
noncomputable def A248123 (n : ℕ) : ℕ :=
  -- Define the $k$-th Catalan number $C(k)$ explicitly.
  let catalan (k : ℕ) : ℕ := (2 * k).choose k / (k + 1)

  -- The sequence value a(n) is the least element (infimum) of the set of candidates.
  sInf {m : ℕ | m > 0 ∧ Nat.gcd m n = 1 ∧ (m * n) ∣ catalan (m + n)}

/-- A248123 Conjecture: a(n) exists for all n > 0. -/
theorem oeis_248123_conjecture_0 (n : ℕ) (hn : n > 0) : A248123 n > 0 := by sorry
