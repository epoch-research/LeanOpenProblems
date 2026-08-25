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
Let $n_1 < n_2 < \dots$ be an infinite sequence with $\frac{n_{k+1}}{n_k} \ge c > 1$. Must
$\sum_k \frac 1 {F_{n_k}}$ be irrational?
-/
theorem erdos_267 : ∀ᵉ (n : ℕ → ℕ) (c > (1 : ℚ)), StrictMono n → (∀ k, c ≤ n (k+1) / n k) →
    Irrational (∑' k, 1 / (Nat.fib <| n k)) := by
  sorry

end Erdos267

theorem Erdos267.erdos_267.disproof : ¬ (type_of% @Erdos267.erdos_267) := sorry
