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
# Erdős Problem 364

*Reference:* [erdosproblems.com/364](https://www.erdosproblems.com/364)
-/

open Nat

namespace Erdos364

/--
Erdős [Er76d] conjectured a stronger statement: if $n_k$ is the $k$th powerful number,
then $n_{k+2} - n_k > n_k^c$ for some constant $c > 0$.

[Er76d] Erdős, P., Problems and results on number theoretic properties of consecutive integers and related questions. Proceedings of the Fifth Manitoba Conference on Numerical Mathematics (Univ. Manitoba, Winnipeg, Man., 1975) (1976), 25-44.
-/
@[category research open, AMS 11]
theorem erdos_364.variants.strong :
    ∃ (c : ℝ) (h : c > 0), ∀ (k : ℕ),
    Nat.nth Powerful (k + 2) - Nat.nth Powerful k > (Nat.nth Powerful k : ℝ) ^ c := by
  sorry

end Erdos364
