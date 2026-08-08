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
When $n = 3$, the answer is 8 (due to Croft [Cr62]).

[Cr62] Croft, H. T., $9$-point and $7$-point configurations in $3$-space. Proc. London Math. Soc. (3) (1962), 400-424.
-/
theorem erdos_503.variants.R3 :
    IsGreatest {(A.ncard) | (A : Set ℝ³) (hA : A.IsIsosceles)} 8 := by
  sorry

end Erdos503
