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

open Nat Finset Set

/--
The product $(k+1)(k+2)\cdots(k+n)$.
-/
def A078729_product (n k : ℕ) : ℕ :=
  (Finset.range n).prod (fun i ↦ k + i + 1)

/--
A078729: $a(n)$ is the least positive integer $k$ such that
$$(k+1)(k+2)\cdots(k+n) + 1$$
is prime, if such $k$ exists; otherwise, $a(n) = 0$.
-/
noncomputable def A078729 (n : ℕ) : ℕ :=
  sInf { k : ℕ | k > 0 ∧ (A078729_product n k + 1).Prime }

/--
Conjecture: $a(n) = 0$ if and only if $n=4$.
-/
theorem oeis_78729_conjecture_0 : ∀ n : ℕ, A078729 n = 0 ↔ n = 4 := by sorry

theorem oeis_78729_conjecture_0.disproof : ¬ (type_of% @oeis_78729_conjecture_0) := sorry
