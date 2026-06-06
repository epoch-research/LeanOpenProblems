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

open Nat Finset Rat
open scoped BigOperators

/--
A060841: Numerator of $1/\det(M)$ where $M$ is the $n \times n$ matrix with $M[i,j] = 1/\operatorname{lcm}(i,j)$.
The value is $\frac{1}{\det(M)} = \prod_{k=1}^n \frac{k^2}{\phi(k)}$
-/
noncomputable def A060841 (n : ℕ) : ℕ :=
  let val_rat : ℚ := (Icc 1 n).prod (fun k : ℕ => ((k : ℚ) ^ 2) / (k.totient : ℚ))
  val_rat.num.natAbs

/-- The rational value $1/\det(M_n) = \prod_{k=1}^n \frac{k^2}{\phi(k)}$. -/
noncomputable def A060841_val_rat (n : ℕ) : ℚ :=
  (Icc 1 n).prod (fun k : ℕ => ((k : ℚ) ^ 2) / (k.totient : ℚ))

/-- Conjecture: 1/det(M) is an integer only for n: 1 - 34, 36 and 38.
All denominators are powers of two (A000079). -/
theorem oeis_60841_conjecture_0 (n : ℕ) (hn : 1 ≤ n) :
  (A060841_val_rat n).den.isPowerOfTwo ∧
  ((A060841_val_rat n).isInt ↔ n ∈ Icc 1 34 ∨ n = 36 ∨ n = 38) :=
by sorry
