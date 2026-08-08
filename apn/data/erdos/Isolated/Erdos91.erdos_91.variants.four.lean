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
# Erdős Problem 91

*Reference:*
- [Er87b] Erdős, P., Some combinatorial and metric problems in geometry.
  Intuitive geometry (Siófok, 1985) (1987), 167-177.
- [Ko24c] Z. Kovács, A note on Erdős's mysterious remark. arXiv:2412.05190 (2024).
- [erdosproblems.com/91](https://www.erdosproblems.com/91)
-/

open Finset EuclideanGeometry Filter

namespace Erdos91

/-- A set $A$ is 'optimal' if it has $n$ points and achieves the minimum distance count. -/
noncomputable def IsOptimal (A : Finset ℝ²) (n : ℕ) : Prop :=
  A.card = n ∧ distinctDistances A = minimalDistinctDistances n

/-- Two finite sets of points in $\mathbb{R}^2$ are similar if one can be mapped to the other by a
DilationEquiv. -/
def DilationEquivSimilar (A B : Finset ℝ²) : Prop :=
  ∃ f : ℝ² ≃ᵈ ℝ², (f '' A) = B

/-- Equilateral triangle with unit side length, resting on the x-axis with one vertex at the origin. -/
noncomputable def equiTriangle : Finset ℝ² := {!₂[0, 0], !₂[1, 0], !₂[1 / 2, Real.sqrt 3 / 2]}

noncomputable def unitSquare : Finset ℝ² := {!₂[0, 0], !₂[0, 1], !₂[1, 0], !₂[1, 1]}

/-- Regular 7-gon with unit side length, touching both axes in the first quadrant. -/
noncomputable def circleSeven : Finset ℝ² :=
  let r := 1 / (2 * Real.sin (Real.pi / 7))
  let cx := r * Real.cos (Real.pi / 7)
  let cy := r * Real.sin (4 * Real.pi / 7)
  (Finset.range 7).image fun k : ℕ =>
    !₂[r * Real.cos (2 * Real.pi * ↑k / 7) + cx, r * Real.sin (2 * Real.pi * ↑k / 7) + cy]

/-- Wheel graph on 7 vertices (center + regular hexagon) with unit side length,
touching both axes in the first quadrant. -/
noncomputable def wheelSeven : Finset ℝ² :=
  {!₂[1, Real.sqrt 3 / 2],
   !₂[2, Real.sqrt 3 / 2],
   !₂[3 / 2, Real.sqrt 3],
   !₂[1 / 2, Real.sqrt 3],
   !₂[0, Real.sqrt 3 / 2],
   !₂[1 / 2, 0],
   !₂[3 / 2, 0]}

/--
The predicate on $n$ asserting all $A, B\subset \mathbb{R}^2$,
with $\lvert A\rvert=n = \lvert B\rvert$, which minimise the number of distinct points for all sets
with $n$ elements are similar.
-/
def UniqueMinimizer (n : ℕ) : Prop :=
  ∀ A B : Finset ℝ², IsOptimal A n → IsOptimal B n → DilationEquivSimilar A B

/--
For $n=4$ the square or two equilateral triangles sharing an edge give two
non-similar examples.
-/
theorem erdos_91.variants.four : ¬ UniqueMinimizer 4 := by
  sorry

end Erdos91
