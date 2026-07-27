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
A333206: $a(n)$ is the least decimal digit of $n^3$.
-/
def a (n : ℕ) : ℕ :=
  (Nat.digits 10 (n ^ 3)).min?.getD 0

/--
This theorem formalizes the contrapositive of the previous claim based on the heuristic:
that there are infinitely many $n$ such that $a(n) \ge 5$.
-/
theorem oeis_333206_conjecture_infiniteness_a_ge_five :
  ∀ (M : ℕ), ∃ (n : ℕ), M ≤ n ∧ 5 ≤ a n :=
  sorry
