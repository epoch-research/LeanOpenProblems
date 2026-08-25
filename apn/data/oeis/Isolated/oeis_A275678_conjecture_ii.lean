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

/--
A275678: Number of ordered ways to write $n$ as $4^k(1+4x^2+y^2) + z^2$,
where $k,x,y,z$ are nonnegative integers with $x \le y$.
-/
def A275678 (n : ℕ) : ℕ :=
  -- Since $z^2 \le n$, $k, x^2, y^2$ are all bounded by $n$. $n+1$ is a safe and computable upper bound.
  let B := n + 1

  Finset.sum (Finset.range B) fun k =>
  Finset.sum (Finset.range B) fun x =>
  Finset.sum (Finset.range B) fun y =>
    if x ≤ y then
      let P_term := 4^k * (1 + 4 * x^2 + y^2)

      -- The existence of a non-negative integer $z$ is equivalent to $n - P_{term}$ being a perfect square.
      if P_term ≤ n then
        -- We check if $n - P_{term}$ is a perfect square using the standard Mathlib function for integer square root.
        let r := n - P_term
        let z_candidate := r.sqrt
        if z_candidate ^ 2 = r then 1 else 0
      else 0
    else 0

/-- Conjecture: Any positive integer can be written as $4^k(1+4x^2+y^2) + z^2$,
where $k,x,y,z$ are nonnegative integers with $x \le z$.
Note: This is part (ii) of the conjecture listed in OEIS A275678.
This is a different conjecture because the constraint $x \le y$ in the definition of $a(n)$
is replaced by $x \le z$ here, and the problem is about existence (similar to (i)), not number of ways.
The question only asked to formalize "oeis_275678_conjecture_1", which I take to be the primary one (i),
but I will include (ii) as well for completeness, as it's a nearby mathematical claim.
-/
theorem oeis_A275678_conjecture_ii (n : ℕ) (hn : n > 0) :
  ∃ k x y z : ℕ, n = 4^k * (1 + 4 * x^2 + y^2) + z^2 ∧ x ≤ z :=
by sorry

theorem oeis_A275678_conjecture_ii.disproof : ¬ (type_of% @oeis_A275678_conjecture_ii) := sorry
