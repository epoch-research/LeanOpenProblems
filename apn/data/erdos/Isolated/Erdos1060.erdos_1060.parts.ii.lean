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
# Erdős Problem 1060

*Reference:* [erdosproblems.com/1060](https://www.erdosproblems.com/1060)
-/

open Asymptotics Finset Filter Real
open scoped ArithmeticFunction.sigma

namespace Erdos1060

/-- Part (ii) of Erdős Problem 1060: bound on the number of $k \le n$ with $k \sigma_1(k) = n$. -/
theorem erdos_1060.parts.ii :
    ∃ (C : ℝ), (fun n ↦ (#{k ≤ n | k * σ 1 k = n} : ℝ)) =O[atTop]
      (fun n ↦ log n ^ C) := by sorry

end Erdos1060

theorem Erdos1060.erdos_1060.parts.ii.disproof : ¬ (type_of% @Erdos1060.erdos_1060.parts.ii) := sorry
