/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 499
*Reference:* [erdosproblems.com/499](https://www.erdosproblems.com/499)
-/

open Nat

namespace Erdos499

/--
A weaker version of Erdős' problem 499, which asks whether for every doubly stochastic matrix, there
exists a permutation $σ \in S_n$ with $M_{i, σ(i)} ≠ 0$ and such that
$$
\sum_{1 \leq i \leq n} M_{i, σ(i)} \geq 1
$$
Proved by Marcus and Ree [MaRe59].

[MaRe59] Marcus, M. and Ree, R., Diagonals of doubly stochastic matrices. Quart. J. Math. Oxford Ser. (2) (1959), 296-302.
-/
lemma erdos_499.variants.one_le :
    ∀ n > 0, ∀ M ∈ doublyStochastic ℝ (Fin n), ∃ σ : Equiv.Perm (Fin n),
      (∀ i, M i (σ i) ≠ 0) ∧ 1 ≤ ∑ i, M i (σ i) := by
  sorry

end Erdos499
