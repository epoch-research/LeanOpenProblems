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

open Nat
open scoped BigOperators

/--
A008347(k): Alternating sum of the first $k$ primes: $p_k - p_{k-1} + \cdots + (-1)^{k-1} p_1$, defined for $k \ge 1$.
We define $A008347(0)=0$ for recursion base case purposes.
$p_k$ is the $k$-th prime (1-indexed), corresponding to $\mathrm{Nat.nth Nat.Prime} (\mathrm{k}-1)$ in Mathlib.
-/
noncomputable def A008347_seq : ℕ → ℕ
  | 0 => 0
  -- A008347(1) = p_1 = 2
  | 1 => Nat.nth Nat.Prime 0
  -- A008347(k+2) = p_{k+2} - A008347(k+1)
  | k + 2 =>
    let p_k_plus_2 := Nat.nth Nat.Prime (k + 1)
    p_k_plus_2 - A008347_seq (k + 1)

/--
A308403: The number of ways to write $n$ as $6^i + 3^j + A008347(k)$, where $i, j \ge 0$ are nonnegative integers and $k \ge 1$ is a positive integer.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let S := A008347_seq
  -- $i$ is bounded by $\log_6 n$, $j$ by $\log_3 n$.
  -- We use a general upper bound $n$ over logarithmic bounds for simplicity and correctness.
  (Finset.range (n + 1)).sum fun i =>
    (Finset.range (n + 1)).sum fun j =>
      let base_sum := 6^i + 3^j
      if base_sum < n then
        let target_m := n - base_sum
        -- Count $k \ge 1$ such that S k = target_m.
        -- We use a computed upper bound that's sufficient to find all solutions $k$.
        -- Since $A008347(k)$ grows, the number of solutions is finite. $2n$ is a loose but correct bound.
        ((Finset.range (2 * n + 2)).filter (fun k => k > 0 ∧ S k = target_m)).card
      else 0

-- Formalization of the claim about verification status for Conjecture 1.
-- The claim: "Conjecture 1 verified up to 10^10"
theorem A308403.conjecture_1_verified_up_to_10_pow_10 :
    ∀ n : ℕ, 2 < n ∧ n ≤ 10000000000 → a n > 0 := by
  sorry

theorem A308403.conjecture_1_verified_up_to_10_pow_10.disproof : ¬ (type_of% @A308403.conjecture_1_verified_up_to_10_pow_10) := sorry
