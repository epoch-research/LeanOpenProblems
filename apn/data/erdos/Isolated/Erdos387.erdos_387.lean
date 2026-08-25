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
# Erdős Problem 387

*References:*
 - [erdosproblems.com/387](https://www.erdosproblems.com/387)
 - [Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.
 - [Fa66] Faulkner, M. "On a theorem of Sylvester and Schur." Journal of the London Mathematical
    Society 1.1 (1966): 107-110.
 -
-/

open Filter

namespace Erdos387

/-- Is there an absolute constant `c > 0` such that, for all `1 ≤ k < n`, the binomial coefficient
`n.choose k` has a divisor in `(cn, n]`? -/
theorem erdos_387 : ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
    ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

end Erdos387

theorem Erdos387.erdos_387.disproof : ¬ (type_of% @Erdos387.erdos_387) := sorry
