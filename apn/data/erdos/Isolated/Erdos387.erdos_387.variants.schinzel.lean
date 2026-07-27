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

/-- The following is Schinzel's conjecture, which appears in [Gu04]. -/
@[category research open, AMS 11]
theorem erdos_387.variants.schinzel : 
    ∀ᶠ k in atTop, ¬ IsPrimePow k → ∃ n : ℕ, ∀ i < k, ¬ n - i ∣ n.choose k := by
  sorry

end Erdos387
