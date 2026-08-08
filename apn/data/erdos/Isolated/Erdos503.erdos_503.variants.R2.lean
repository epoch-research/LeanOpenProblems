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
When $n = 2$, the answer is 6 (due to Kelly [ErKe47] - an alternative proof is given by Kovács [Ko24c]).

[ErKe47] Erdős, Paul and Kelly, L. M., Elementary Problems and Solutions: Solutions: E735. Amer. Math. Monthly (1947), 227-229.
[Ko24c] Z. Kovács, A note on Erdős's mysterious remark. arXiv:2412.05190 (2024).
-/
theorem erdos_503.variants.R2 :
    IsGreatest {(A.ncard) | (A : Set ℝ²) (hA : A.IsIsosceles)} 6 := by
  sorry

end Erdos503
