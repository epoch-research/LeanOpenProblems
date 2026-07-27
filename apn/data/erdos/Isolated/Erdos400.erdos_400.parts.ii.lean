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
# Erdős Problem 400

*Reference:* [erdosproblems.com/400](https://www.erdosproblems.com/400)
-/

open Nat Filter Finset
open scoped Asymptotics Topology

namespace Erdos400

/--
For any $k\geq 2$ let $g_k(n)$ denote the maximum value of $(a_1+\cdots+a_k)-n$
where $a_1,\ldots,a_k$ are integers such that $a_1!\cdots a_k! \mid n!$.
-/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup { ((∑ i, a i) - n) | (a : Fin k → ℕ) (_ : (∏ i, (a i) !) ∣ n !) }

/--
Is it true that there is a constant $c_k$ such that for almost all $n < x$ we have
$g_k(n)=c_k\log x+o(\log x)$?
-/
@[category research open, AMS 11]
theorem erdos_400.parts.ii :
    ∀ᵉ (k ≥ 2), ∃ c : ℝ, ∀ ε > 0,
      Tendsto (fun x : ℕ ↦
        (((Icc 1 x).filter (fun n ↦
          |(g k n : ℝ) - c * Real.log x| ≤ ε * Real.log x)).card : ℝ) / x)
        atTop (𝓝 1) := by
  sorry

end Erdos400
