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
# Conjectures about the Mandelbrot and Multibrot sets
This file adds three conjectures about the Mandelbrot and Multibrot sets:
- the *MLC conjecture*, stating that these sets are locally connected
- the *density of hyperbolicity* conjecture, stating that parameters with attracting cycles are
  dense in the Mandelbrot and Multibrot sets
- the conjecture that the boundaries of these sets have zero area.
The first two conjectures are related in that the former implies the latter.

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Mandelbrot_set#Local_connectivity)
 - [arxiv/math/9902155](https://arxiv.org/abs/math/9902155)
 - [mathoverflow/37229](https://mathoverflow.net/questions/37229/)
-/

open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- The Multibrot set of power `n` is the set of all parameters `c : ℂ` for which `0` does not
escape to infinity under repeated application of `z ↦ z ^ n + c`. -/
def multibrotSet (n : ℕ) : Set ℂ :=
  {c | ¬ Tendsto (fun k ↦ (fun z ↦ z ^ n + c)^[k] 0) atTop (cobounded ℂ)}

/-- The Mandelbrot set is the special case of the multibrot set for n = 2. In other words, it is the
set of all parameters `c : ℂ` for which `0` does not escape to infinity under repeated application
of `z ↦ z ^ 2 + c`. -/
abbrev mandelbrotSet := multibrotSet 2

/-- We say that `z : ℂ` is part of an attracting cycle of period `n` of `f : ℂ → ℂ` if it is an
`n`-periodic point (i.e. `f^[n] z = z`), `f^[n]` is differentiable at `z`, `‖deriv f^[n] z‖` is
strictly less than one, and `n > 0`. -/
def IsAttractingCycle (f : ℂ → ℂ) (n : ℕ) (z : ℂ) : Prop :=
  (0 < n) ∧ f.IsPeriodicPt n z ∧ DifferentiableAt ℂ f^[n] z ∧ ‖deriv f^[n] z‖ < 1

/-- The boundary of the Mandelbrot set is conjectured to have zero area. -/
theorem volume_frontier_mandelbrotSet_eq_zero : volume (frontier mandelbrotSet) = 0 := by
  sorry

end Mandelbrot

theorem Mandelbrot.volume_frontier_mandelbrotSet_eq_zero.disproof : ¬ (type_of% @Mandelbrot.volume_frontier_mandelbrotSet_eq_zero) := sorry
