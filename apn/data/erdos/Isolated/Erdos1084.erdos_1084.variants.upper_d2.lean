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
# Erdős Problem 1084

*Reference:* [erdosproblems.com/1084](https://www.erdosproblems.com/1084)

Let `f_2(n)` be the maximum number of pairs of points at distance exactly `1`
among any set of `n` points in `ℝ²`, under the condition that all pairwise
distances are at least `1`.

Estimate the growth of `f_2(n)`.

Status: open.
-/

open Finset Filter Metric Real
open scoped EuclideanGeometry

namespace Erdos1084
variable {n : ℕ}

/-- The maximal number of pairs of points which are distance 1 apart that a set of `n` 1-separated
points in `ℝ^d` make. -/
noncomputable def f (d n : ℕ) : ℕ :=
  ⨆ (s : Finset (ℝ^ d)) (_ : s.card = n) (_ : IsSeparated' 1 (s : Set (ℝ^ d))), unitDistNum s

-- TODO: Add erdos_1084.

/-- Erdős showed that there is some constant $c > 0$ such that $f_2(n) < 3n - c n^{1/2}$. -/
theorem erdos_1084.variants.upper_d2 : ∃ c > (0 : ℝ), ∀ n > 0, f 2 n < 3 * n - c * sqrt n := by
  sorry

end Erdos1084
