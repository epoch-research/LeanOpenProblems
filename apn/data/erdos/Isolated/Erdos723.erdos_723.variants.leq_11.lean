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
# Erdős Problem 723: The prime power conjecture.

*Reference:* [erdosproblems.com/723](https://www.erdosproblems.com/723)
-/

open Configuration

namespace Erdos723

/--
This conjecture has been proved for $n \leq 11$.
-/
theorem erdos_723.variants.leq_11 {P L : Type} [Membership P L] [Fintype P] [Fintype L] :
    ∀ pp : ProjectivePlane P L, pp.order ≤ 11 → IsPrimePow pp.order := by
  sorry

end Erdos723
