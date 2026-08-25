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

/--
A096535: $a(0) = a(1) = 1$; $a(n) = (a(n-1) + a(n-2)) \bmod n$.
-/
def A096535 : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => (A096535 (n + 1) + A096535 n) % (n + 2)

/--
A096535 Three conjectures: (1) All numbers appear infinitely often, i.e., for every number k >= 0 and every frequency f > 0 there is an index i such that a(i) = k is the f-th occurrence of k in the sequence.
-/
theorem oeis_a096535_conjecture_1 :
  ∀ (k : ℕ), ∀ (N : ℕ), ∃ (i : ℕ), i > N ∧ A096535 i = k := by
  sorry

theorem oeis_a096535_conjecture_1.disproof : ¬ (type_of% @oeis_a096535_conjecture_1) := sorry
