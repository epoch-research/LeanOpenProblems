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

open Nat Set ArithmeticFunction

/--
A076495: Smallest $x$ such that $\sigma(x) \bmod x = n$, or $0$ if no such $x$ exists.
-/
noncomputable def A076495 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x ≠ 0 ∧ (sigma 1 x) % x = n }

/--
A076495 At present, the 0 entry for n=5 is only a conjecture.
That is, it is conjectured that there is no positive natural number $x$ such that
$\sigma_1(x) \bmod x = 5$.
-/
theorem oeis_76495_conjecture_0 : A076495 5 = 0 := by sorry

theorem oeis_76495_conjecture_0.disproof : ¬ (type_of% @oeis_76495_conjecture_0) := sorry
