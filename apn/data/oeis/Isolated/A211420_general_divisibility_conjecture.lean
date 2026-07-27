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
A211420: $a(n) = \frac{(8n)! n!}{(4n)! (3n)! (2n)!}$
Since the OEIS entry states that this ratio is always an integer, we define it directly as a natural number.
The division in Lean's `Nat` type is integer division, which is exact here.
-/
def A211420 (n : ℕ) : ℕ :=
  (8 * n).factorial * n.factorial / ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial)

/--
General Conjecture:
There are constants $C(k, r)$, for $k \in \{1, 2, 3\}$ and $r \ge 1$,
such that $a(n) \cdot C(k, r) / ((k \cdot n + 1)(k \cdot n + 2)\cdots(k \cdot n + r))$ is an integer for all $n$.
The denominator product $\prod_{i=1}^r (k \cdot n + i)$ is formalized using Nat.ascFactorial,
where $\text{ascFactorial } x r = x(x+1)\cdots(x+r-1)$.
Letting $x = k \cdot n + 1$ gives the desired product.
-/
theorem A211420_general_divisibility_conjecture :
  ∀ (k : ℕ) (r : ℕ), (k = 1 ∨ k = 2 ∨ k = 3) → (r ≥ 1) → ∃ C : ℕ, ∀ n : ℕ,
    Nat.ascFactorial (k * n + 1) r ∣ C * (A211420 n) :=
by sorry
