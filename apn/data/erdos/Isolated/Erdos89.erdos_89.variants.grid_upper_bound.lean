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
# Erdős Problem 89

*References:*
- [erdosproblems.com/89](https://www.erdosproblems.com/89)
- [Er46] Erdős, Paul. On sets of distances of $n$ points. Amer. Math. Monthly
  53 (1946), 248--250.
- [GuKa15] Guth, Larry and Katz, Nets Hawk. On the Erdős distinct distances
  problem in the plane. Ann. of Math. (2) 181 (2015), 155--190.
- [Mo52] Moser, Leo. On the different distances determined by $n$ points.
  Amer. Math. Monthly 59 (1952), 85--91.

### AI disclosure

Lean 4 code in this file was drafted with assistance from OpenAI Codex.
The mathematical content and references are the author's own work.
-/

open Filter
open EuclideanGeometry

namespace Erdos89

/--
The square grid construction, going back to Erdős and Moser, shows that
$\frac{n}{\sqrt{\log n}}$ is the correct order if the conjecture is true:
there are configurations whose number of distinct distances is
$O(\frac{n}{\sqrt{\log n}})$.
-/
theorem erdos_89.variants.grid_upper_bound :
    (fun n => (minimalDistinctDistances n : ℝ)) =O[atTop]
      (fun (n : ℕ) => n/(n : ℝ).log.sqrt) := by
  sorry

-- TODO(firsching): formalize any remaining remarks from the erdosproblems.com page.

end Erdos89

theorem Erdos89.erdos_89.variants.grid_upper_bound.disproof : ¬ (type_of% @Erdos89.erdos_89.variants.grid_upper_bound) := sorry
