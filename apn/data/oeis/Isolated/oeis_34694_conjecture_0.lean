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
A034694: Smallest prime $\equiv 1 \pmod n$.
$$a(n) = \min \{p \in \mathbb{P} \mid p \equiv 1 \pmod n \}$$
-/
noncomputable def A034694 (n : ℕ) : ℕ :=
  -- The set infimum, sInf, gives the smallest element of the set of natural numbers.
  sInf {p : ℕ | Nat.Prime p ∧ n ∣ (p - 1)}

/-- OEIS A034694 Conjecture: a(n) < n^2 for n > 1. - Thomas Ordowski, Dec 19 2016 -/
theorem oeis_34694_conjecture_0 (n : ℕ) (h : 1 < n) :
  A034694 n < n ^ 2 := by sorry

theorem oeis_34694_conjecture_0.disproof : ¬ (type_of% @oeis_34694_conjecture_0) := sorry
