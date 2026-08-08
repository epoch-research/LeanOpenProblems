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
Good [Go74] and Bicknell and Hoggatt [BiHo76] have shown that $\sum_n \frac 1 {F_{2^n}}$ is irrational.
Ref:
* [Go74] Good, I. J., _A reciprocal series of Fibonacci numbers_
* [BiHo76] Hoggatt, Jr., V. E. and Bicknell, Marjorie, _A reciprocal series of Fibonacci numbers with subscripts $2\sp{n}k$_
-/
theorem erdos_267.variants.specialization_pow_two :
    Irrational <| ∑' k, 1 / (Nat.fib <| 2^k) := by
  sorry

end Erdos267
