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
# Erdős Problem 195

*References:*
- [erdosproblems.com/195](https://www.erdosproblems.com/195)
- [Ad22] Adenwalla, S., Avoiding Monotone Arithmetic Progressions in Permutations of Integers.
  arXiv:2211.04451 (2022).
- [Ge19] Geneson, Jesse, Forbidden arithmetic progressions in permutations of subsets of the
  integers. Discrete Math. (2019), 1489-1491.
-/

namespace Erdos195

/--
Adenwalla [Ad22] proved that k ≤ 4.
-/
theorem erdos_195.variants.leq_4_bound :
    4 ≥ sSup {k : ℕ | ∀ f : ℤ ≃ ℤ, HasMonotoneAP f k} := by
  sorry

end Erdos195
