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
# Erdős Problem 409

*Reference:* [erdosproblems.com/409](https://www.erdosproblems.com/409)
-/

open scoped Topology ArithmeticFunction.sigma Nat
open Filter

namespace Erdos409

/-- If $n > 1$ then the iteration $n\mapsto\sigma(n) - 1$ necessarily reaches a prime.
Note: this is open — it is not clear that the σ iteration always terminates,
since it is non-decreasing (unlike the φ iteration which is strictly decreasing). -/
theorem erdos_409.variants.sigma_termination (n : ℕ) (hn : n > 1) :
    ∃ i, (σ 1 · - 1)^[i] n |>.Prime := by
  sorry

end Erdos409
