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
# Erdős Problem 392

*Reference:* [erdosproblems.com/392](https://www.erdosproblems.com/392)
-/

open Filter

open scoped Nat

namespace Erdos392

/--
Cambie has observed that a positive answer follows from the result above with $a_t \leq n$, simply
by pairing variables together, e.g. taking $a'_i = a_{2i-1}a_{2i}$ (and the lower bound follows from
Stirling's approximation).
-/
theorem erdos_392.variants.implication (h : type_of% erdos_392) :
    type_of% erdos_392.variants.lower := by
  sorry

end Erdos392
