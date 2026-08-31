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
Mahler proved $(1_A \ast 1_A)(n) \gg (\log n)^{1/4}$ for infinitely many $n$, where $A$ is
the set of perfect cubes.

[Ma35b] Mahler, K., _On the lattice points on curves of genus 1_. Proc. London Math. Soc.
  (2) (1935), 431-466.
-/
theorem mahler : ∃ C > (0 : ℝ),
    ∃ᶠ (n : ℕ) in atTop, C * (Real.log n) ^ ((1 : ℝ) / 4) ≤ (sumRep cubes n : ℝ) := by
  sorry

end variants

end Erdos829

theorem Erdos829.variants.mahler.disproof : ¬ (type_of% @Erdos829.variants.mahler) := sorry
