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

/-!
# Erdős Problem 1210

*References:*
- [erdosproblems.com/1210](https://www.erdosproblems.com/1210)
- [Er77c] Erdős, Paul, Problems and results on combinatorial number theory. III. Number theory day
  (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43-72.
- [Er80] Erdős, Paul, A survey of problems in combinatorial number theory. Ann. Discrete Math.
  (1980), 89-115.
-/

open Finset

namespace Erdos1210

/--
In [Er80] he claims he "did not state this quite correctly" in [Er77c]. The problem in [Er77c] which
Erdős is presumably referring to states that if $n < q_1 < \cdots < q_k\leq m$ is the set of primes
in $(n,m]$ then $\sum \frac{1}{q_i-n} < \sum_{p < m-n}\frac{1}{p}+O(1)$.
-/
theorem erdos_1210.variants.er80_correction :
  
    ∃ C : ℝ, ∀ n m : ℕ, n < m →
      ∑ q ∈ (Ioc n m).filter Prime, (1 / ((q : ℝ) - n)) <
      (∑ p ∈ (range (m - n)).filter Prime, (1 / (p : ℝ))) + C := by
  sorry

end Erdos1210
