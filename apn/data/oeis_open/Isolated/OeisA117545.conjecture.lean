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

import FormalConjecturesUtil

/-!
# Least $k$ such that cyclotomic polynomial $\Phi_k(n)$ is prime

$a(n) = \min \{k \in \mathbb{N} \mid 0 < k \wedge \text{Prime}(|\Phi_k(n)|) \}$,
where $\Phi_k(n)$ is the $k$-th cyclotomic polynomial evaluated at $n$.

*References:*
- [A117545](https://oeis.org/A117545)-/

namespace OeisA117545

/-- Least $k > 0$ such that $|\Phi_k(n)|$ is prime, or $0$ if no such $k$ exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ ((Polynomial.cyclotomic k ℤ).eval (n : ℤ)).natAbs.Prime}

/--
Is $a(n)$ defined for all $n \ge 1$?
That is, for every $n \ge 1$, does there exist $k > 0$ such that $|\Phi_k(n)|$ is prime?-/
theorem conjecture (n : ℕ) (hn : 0 < n) :
    ∃ k > 0, ((Polynomial.cyclotomic k ℤ).eval (n : ℤ)).natAbs.Prime := by
  sorry

end OeisA117545

theorem OeisA117545.conjecture.disproof : ¬ (type_of% @OeisA117545.conjecture) := sorry
