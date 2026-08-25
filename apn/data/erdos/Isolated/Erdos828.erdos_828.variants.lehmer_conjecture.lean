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
# Erdős Problem 828

*Reference:* [erdosproblems.com/828](https://www.erdosproblems.com/828)
-/

namespace Erdos828

open scoped Nat

/--
When $n > 1$, Lehmer conjectured that $\phi(n) | n - 1$ if and only if $n$ is prime.
-/
theorem erdos_828.variants.lehmer_conjecture : ∀ n > 1, φ n ∣ n - 1 ↔ Prime n := by
  sorry

end Erdos828

theorem Erdos828.erdos_828.variants.lehmer_conjecture.disproof : ¬ (type_of% @Erdos828.erdos_828.variants.lehmer_conjecture) := sorry
