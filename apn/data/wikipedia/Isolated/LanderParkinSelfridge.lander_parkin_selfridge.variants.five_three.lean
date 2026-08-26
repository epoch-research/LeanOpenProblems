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

import FormalConjecturesUtil

/-!
# Lander, Parkin, and Selfridge Conjecture

**Reference:** https://en.wikipedia.org/wiki/Lander,_Parkin,_and_Selfridge_conjecture
-/

namespace LanderParkinSelfridge

/-- Special case of the Lander–Parkin–Selfridge conjecture: there is no solution in positive
integers to
$$x_1^5 + x_2^5 + x_3^5 = y^5.$$
That is, for all $x_1, x_2, x_3, y \in \mathbb{N}$ with $x_1, x_2, x_3, y > 0$,
$$x_1^5 + x_2^5 + x_3^5 \neq y^5.$$
This corresponds to the case $k = 5$, $n = 3$, $m = 1$ of the general conjecture,
where $n + m = 4 < 5 = k$ would be required to yield a counterexample. -/
theorem lander_parkin_selfridge.variants.five_three :
    ∀ x₁ x₂ x₃ y : ℕ,
      0 < x₁ → 0 < x₂ → 0 < x₃ → 0 < y →
      x₁ ^ 5 + x₂ ^ 5 + x₃ ^ 5 ≠ y ^ 5 := by
  sorry

end LanderParkinSelfridge
