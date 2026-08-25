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
# Erdős Problem 829

*References:*
- [erdosproblems.com/829](https://www.erdosproblems.com/829)
- [Er83] Erdős, P. and Dudley, U., _Some remarks and problems in number theory related to the
  work of Euler_. Math. Mag. (1983), 292-298.
-/

open AdditiveCombinatorics Asymptotics Filter

namespace Erdos829

/-- The set of perfect cubes in $\mathbb{N}$. -/
def cubes : Set ℕ := {n | ∃ k, k ^ 3 = n}

namespace variants

/--
Stewart improved Mahler's lower bound to $(1_A \ast 1_A)(n) \gg (\log n)^{11/13}$ for
infinitely many $n$, where $A$ is the set of perfect cubes.

[St08] Stewart, C. L., _Cubic Thue equations with many solutions_. Int. Math. Res. Not.
  IMRN (2008), Art. ID rnn040, 11.
-/
theorem stewart : ∃ C > (0 : ℝ),
    ∃ᶠ (n : ℕ) in atTop, C * (Real.log n) ^ ((11 : ℝ) / 13) ≤ (sumRep cubes n : ℝ) := by
  sorry

end variants

end Erdos829
