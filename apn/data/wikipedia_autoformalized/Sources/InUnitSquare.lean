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

import FormalConjecturesUtil

/-!
# Unit square: the rational distance problem

The unit square is the square in the Cartesian plane with corners
$(0, 0)$, $(1, 0)$, $(1, 1)$ and $(0, 1)$. It is not known whether any point in the
plane is at rational distance from all four of these vertices.

*References:*
- [Wikipedia: Unit square](https://en.wikipedia.org/wiki/Unit_square#Rational_distance_problem)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- D19 in [Unsolved Problems in Number Theory](https://doi.org/10.1007/978-0-387-26677-0)
by *Richard K. Guy*

See also `FormalConjectures.Wikipedia.RationalDistanceProblem` for another formalization
of the same problem.
-/

namespace InUnitSquare

open EuclideanGeometry

/--
Does there exist a point $P$ in the plane $\mathbb{R}^2$ (not necessarily inside the square)
whose Euclidean distances to the four vertices $(0, 0)$, $(1, 0)$, $(1, 1)$, $(0, 1)$ of the
unit square are all rational?
-/
@[category research open, AMS 11 51]
theorem in_unit_square :
    answer(sorry) ↔ ∃ P : ℝ², ∀ c ∈ ({!₂[0, 0], !₂[1, 0], !₂[1, 1], !₂[0, 1]} : Set ℝ²),
      ∃ q : ℚ, dist P c = q := by
  sorry

end InUnitSquare
