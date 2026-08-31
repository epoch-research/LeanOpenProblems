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
A119591: Least $k \ge 1$ such that $2 \cdot n^k - 1$ is prime.
The sequence starts at $n=2$, so we return 0 for $n < 2$.
-/
noncomputable def A119591 (n : ℕ) : ℕ :=
  if h : n ≥ 2 then
    -- The minimum element of the set of positive integers k for which 2 * n^k - 1 is prime.
    let S : Set ℕ := {k : ℕ | 0 < k ∧ Nat.Prime (2 * n ^ k - 1)}
    sInf S
  else
    0

/-- OEIS A119591 Conjecture: a(n) is defined for all n. -/
theorem oeis_119591_conjecture_0 :
  ∀ n : ℕ, n ≥ 2 → ∃ k : ℕ, 0 < k ∧ Nat.Prime (2 * n ^ k - 1) :=
by sorry

theorem oeis_119591_conjecture_0.disproof : ¬ (type_of% @oeis_119591_conjecture_0) := sorry
