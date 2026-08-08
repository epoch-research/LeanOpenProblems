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
# Erdős Problem 189

*Reference:* [erdosproblems.com/189](https://www.erdosproblems.com/189)
-/

open Affine EuclideanGeometry

namespace Erdos189

/-- Erdős problem 189 asked whether the below holds for all rectangles. -/
def Erdos189For (P : ℝ² → ℝ² → ℝ² → ℝ² → Prop) (A : ℝ² → ℝ² → ℝ² → ℝ² → ℝ) :=
    ∀ᵉ (n > 0) (colouring : ℝ² → Fin n), ∃ colour, ∀ area > (0 : ℝ), ∃ a b c d,
      {a, b, c, d} ⊆ colouring⁻¹' {colour} ∧
      IsCcwConvexPolygon ![a, b, c, d] ∧
      A a b c d = area ∧
      P a b c d

/--
Seems to be open, as of January 2025.
-/
theorem erdos_189.variants.parallelogram :
    ¬ Erdos189For
      (fun a b c d ↦
        line[ℝ, a, b] ∥ line[ℝ, c, d] ∧
        line[ℝ, a, d] ∥ line[ℝ, b, c])
      (fun a b c d ↦ dist a b * dist b c * (∡ a b c).sin) := by
  sorry

end Erdos189
