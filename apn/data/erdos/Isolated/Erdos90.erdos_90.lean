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
# Erdős Problem 90: The unit distance problem

*Reference:* [erdosproblems.com/90](https://www.erdosproblems.com/90)
-/

open Filter
open scoped EuclideanGeometry

namespace Erdos90
open Finset

/--
Given a finite set of points, this function counts the number of **unordered pairs** of distinct
points that are at a distance of exactly 1 from each other.
-/
noncomputable def unitDistancePairsCount (points : Finset ℝ²) : ℕ :=
  (points.offDiag.filter (fun p => dist p.1 p.2 = 1)).card / 2

/--
The set of all possible numbers of unit distances for a configuration of $n$ points.
-/
noncomputable def unitDistanceCounts (n : ℕ) : Set ℕ :=
  {unitDistancePairsCount points | (points : Finset ℝ²) (_ : points.card = n)}

/--
The **maximum number of unit distances** determined by any set of $n$ points in the plane.
This function is often denoted as $u(n)$ in combinatorics.
-/
noncomputable def maxUnitDistances (n : ℕ) : ℕ :=
  sSup (unitDistanceCounts n)

/--
Does every set of $n$ distinct points in $\mathbb{R}^2$ contain at most
$n^{1+O(\frac{1}{\log\log n})}$ many pairs which are distance $1$ apart?
-/
theorem erdos_90 : ∃ (O : ℕ → ℝ) (hO : O =O[atTop] (fun n => 1 / (n : ℝ).log.log)),
    (fun n => (maxUnitDistances n : ℝ)) =ᶠ[atTop] fun (n : ℕ) => (n : ℝ) ^ (1 + O n) := by
  sorry

-- TODO(firsching): add the statements from the rest of the page.

end Erdos90

theorem Erdos90.erdos_90.disproof : ¬ (type_of% @Erdos90.erdos_90) := sorry
