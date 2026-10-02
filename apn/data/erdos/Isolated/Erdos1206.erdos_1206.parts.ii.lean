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
# Erdős Problem 1206

*References:*
- [erdosproblems.com/1206](https://www.erdosproblems.com/1206)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [GGK26] M. Garaev, F. Garayev, and S. Konyagin, *On Sidon sets with squares, cubes, and quartics
  in short intervals*. arXiv:2602.08807 (2026).
- [GaKo24] Gabdullin, M. R. and Konyagin, S. V., *Trigonometric polynomials with frequencies in the
  set of cubes*. Math. Notes (2024), 336--340.
-/

namespace Erdos1206

/--
Is there an infinite set $A\subset \mathbb{N}$ of positive density such that $\{a^3 : a\in A\}$ is a Sidon set?
-/
theorem erdos_1206.parts.ii : 
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  sorry

end Erdos1206

theorem Erdos1206.erdos_1206.parts.ii.disproof : ¬ (type_of% @Erdos1206.erdos_1206.parts.ii) := sorry
