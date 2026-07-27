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
# Erdős Problem 267

*Reference:* [erdosproblems.com/267](https://www.erdosproblems.com/267)
-/

namespace Erdos267

/--
Let $F_1=F_2=1$ and $F_{n+1} = F_n + F_{n-1}$ be the Fibonacci sequence.
Let $n_1 < n_2 < \dots$ be an infinite sequence with $\frac {n_k}{k} \to \infty$. Must
$\sum_k \frac 1 {F_{n_k}}$ be irrational?
-/
@[category research open, AMS 11]
theorem erdos_267.variants.generalisation_ratio_limit_to_infinity : ∀ (n : ℕ → ℕ),
    StrictMono n → Filter.Tendsto (fun k => (n (k+1) / k.succ : ℝ)) Filter.atTop Filter.atTop →
    Irrational (∑' k, 1 / (Nat.fib <| n k)) := by
  sorry

end Erdos267
