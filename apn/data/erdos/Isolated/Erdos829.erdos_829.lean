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

/--
**Erdős Problem 829 (open).**  Let $A \subseteq \mathbb{N}$ be the set of perfect cubes.  Is
it true that $(1_A \ast 1_A)(n) \ll (\log n)^{O(1)}$?  That is, does there exist a natural
number $C$ such that the number of representations of $n$ as a sum of two cubes is
$O((\log n)^C)$ as $n \to \infty$?
-/
theorem erdos_829 :
    
      ∃ C : ℕ, (fun n : ℕ => (sumRep cubes n : ℝ)) =O[atTop]
        (fun n : ℕ => (Real.log n) ^ C) := by
  sorry

namespace variants

end variants

end Erdos829
