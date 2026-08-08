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

/-!
# Erdős Problem 886

*References:*
- [erdosproblems.com/886](https://www.erdosproblems.com/886)
- [ErRo97] Erdős, Paul and Rosenfeld, Moshe, The factor-difference set of integers. Acta Arith.
  (1997), 353--359.
-/

open Nat Filter

namespace Erdos886

/--
The set of divisors of $n$ in the interval $(n^{1/2}, n^{1/2} + n^{1/2-\epsilon})$.
-/
noncomputable def Erdos886Divisors (n : ℕ) (ε : ℝ) (C : ℝ) : Finset ℕ :=
  (divisors n).filter (fun d =>
    (n : ℝ) ^ (1/2 : ℝ) < d ∧ (d : ℝ) < (n : ℝ) ^ (1/2 : ℝ) + C * (n : ℝ) ^ (1/2 - ε))

/--
Erdős and Rosenfeld [ErRo97] proved that there are infinitely many $n$ such that there are
four divisors of $n$ in $(n^{1/2},n^{1/2}+16n^{1/4})$.
-/
theorem erdos_886.variants.rosenfeld_infinite :
    Set.Infinite {n | 4 ≤ (Erdos886Divisors n (1/4) 16).card} := by
  sorry

end Erdos886
