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
# Erdős Problem 100
*References:*
* [erdosproblems.com/100](https://www.erdosproblems.com/100)
* [Kanold](No references found)
* [GuKa15](Guth, Larry and Katz, Nets Hawk, On the Erd\H{o}s distinct distances problem in the plane. Ann. of Math. (2) (2015), 155-190.)
* [Piepmeyer](No references found)
-/

open Set Metric Filter Real
open scoped EuclideanGeometry

namespace Erdos100

/-- If two distances in A differ, they differ by at least 1. -/
def DistancesSeparated (A : Finset ℝ²) : Prop :=
  ∀ p₁ q₁ p₂ q₂, p₁ ∈ A → q₁ ∈ A → p₂ ∈ A → q₂ ∈ A →
    dist p₁ q₁ ≠ dist p₂ q₂ →
    |dist p₁ q₁ - dist p₂ q₂| ≥ 1

/-- Stronger conjecture: diameter $\geq n - 1$ for sufficiently large $n$. -/
theorem erdos_100.variants.strong :
    ∀ᶠ n in atTop, ∀ A : Finset ℝ²,
      A.card = n →
      DistancesSeparated A →
      diam (A : Set ℝ²) ≥ n - 1 := by
  sorry

end Erdos100
