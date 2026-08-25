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
# Erdős Problem 218

*Reference:* [erdosproblems.com/218](https://www.erdosproblems.com/218)
-/

namespace Erdos218

/--
The set of indices $n$ for which a prime gap is preceeded by a larger or equal prime gap has a
natural density of $\frac 1 2$.
-/
theorem erdos_218.variants.ge : {n | primeGap (n + 1) ≤ primeGap n}.HasDensity <| 1 / 2 := by
  sorry

end Erdos218

theorem Erdos218.erdos_218.variants.ge.disproof : ¬ (type_of% @Erdos218.erdos_218.variants.ge) := sorry
