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
Bruck and Ryser have proved that if $n \equiv 1 (\mod 4)$ or $n \equiv 2 (\mod 4)$ then $n$ must be
the sum of two squares.
-/
theorem erdos_723.variants.bruck_ryser {P L : Type} [Membership P L] [Fintype P] [Fintype L]
    (n : ℕ) (pp : ProjectivePlane P L) (hpp : pp.order = n) :
    (n ≡ 1 [MOD 4] ∨ n ≡ 2 [MOD 4]) → ∃ a b, n = a ^ 2 + b ^ 2 := by
  sorry

end Erdos723
