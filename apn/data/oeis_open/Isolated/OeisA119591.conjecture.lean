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
# Least $k \ge 1$ such that $2 \cdot n^k - 1$ is prime

$a(n) = \min \{k \ge 1 \mid \text{Prime}(2 \cdot n^k - 1)\}$ for $n \ge 2$.

*References:*
- [A119591](https://oeis.org/A119591)-/

namespace OeisA119591

/-- Least $k \ge 1$ such that $2 \cdot n^k - 1$ is prime, or $0$ if no such $k$ exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ (2 * n ^ k - 1).Prime}

/--
Is $a(n)$ defined for all $n \ge 2$?
That is, does there exist $k > 0$ such that $2 \cdot n^k - 1$ is prime?-/
theorem conjecture (n : ℕ) (hn : 2 ≤ n) : ∃ k > 0, (2 * n ^ k - 1).Prime := by
  sorry

end OeisA119591
