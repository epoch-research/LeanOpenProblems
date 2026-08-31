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

open ArithmeticFunction Finset Nat

/--
A080326: Denominator of $\sum_{k=1}^n k^{\mu(k)}$, where $\mu$ is the Moebius function (A008683).
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Icc 1 n) fun k : ℕ =>
    (k : ℚ) ^ (moebius k : ℤ)
  ).den

/--
Does a(n) = A034386(n) for infinitely many n?
Conjecture: The set of $n$ such that $a(n)$ equals the primorial of $n$ is infinite.
A034386(n) is `Nat.primorial n`.
-/
theorem oeis_a080326_eq_primorial_infinitely_often :
    Set.Infinite {n : ℕ | a n = primorial n} := by
  sorry

theorem oeis_a080326_eq_primorial_infinitely_often.disproof : ¬ (type_of% @oeis_a080326_eq_primorial_infinitely_often) := sorry
