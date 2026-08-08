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

/--
Can infinitely many $n$ reach the same prime under the iteration $n\mapsto\phi(n) + 1$?
-/
theorem erdos_409.parts.ii :
    ∃ (p : ℕ) (hp : p.Prime), { n | ∃ i, (φ · + 1)^[i] n = p }.Infinite := by
  sorry

end Erdos409
