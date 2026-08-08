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
# Erdős Problem 513

*Reference:*
 - [erdosproblems.com/513](https://www.erdosproblems.com/513)
 - [ClHa64] Clunie, J. and Hayman, W. K., The maximum term of a power series. J. Analyse Math.
  (1964), 143-186.
-/

open scoped Nat Real
open Filter Polynomial

namespace Erdos513

noncomputable def ratio (r : ℝ) (f : ℂ → ℂ) : ℝ :=
  (⨆ n, ‖iteratedDeriv n f 0 * (n ! : ℝ)⁻¹ * r ^ n‖) / (⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖)

/-- For all transcendental entire function `f`, `liminf (fun r : ℝ => ratio r f) atTop > 1 / 2`. -/
theorem erdos_513.variants.lower_bound :
    ⨆ f : {f : ℂ → ℂ // Transcendental ℂ[X] f ∧ Differentiable ℂ f},
    (liminf (fun r : ℝ => ratio r f) atTop) > 1 / 2 := by
  sorry

end Erdos513
