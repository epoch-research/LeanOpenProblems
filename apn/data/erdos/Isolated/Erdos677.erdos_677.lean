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
# Erdős Problem 677
*Reference:* [erdosproblems.com/677](https://www.erdosproblems.com/677)
-/

namespace Erdos677

open Finset

/--
Denote by $M(n, k)$ the least common multiple of the finite set $\{n+1, \dotsc, n+k\}$.
Is it true that for all $m \geq n + k$, we get $M(m, k) \neq M(n, k)$?
-/
theorem erdos_677 :
    ∀ (m n k : ℕ), k > 0 → m ≥ n + k → lcmInterval m k ≠ lcmInterval n k := by
  sorry

-- TODO: Add the other statements from the reference.
