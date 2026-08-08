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
# Erdős Problem 503

*Reference:* [erdosproblems.com/503](https://www.erdosproblems.com/503)
-/

namespace Erdos503

open scoped EuclideanGeometry

/--
The best upper bound known in general is due to Blokhius [Bl84] who showed that
$$
|A| \leq \binom{n + 2}{2}
$$

[Bl84] Blokhuis, A., Few-distance sets. (1984), iv+70.
-/
theorem erdos_503.variants.upper_bound (n : ℕ) :
    ∀ m ∈ {(A.ncard) | (A : Set (ℝ^n)) (hA : A.IsIsosceles)}, m ≤ (n + 2).choose 2 := by
  sorry

end Erdos503
