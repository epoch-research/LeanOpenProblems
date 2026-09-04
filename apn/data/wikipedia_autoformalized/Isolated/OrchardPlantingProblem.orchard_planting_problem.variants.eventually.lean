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
# Orchard-planting problem

The orchard-planting problem asks for the maximum number $t_3^{\text{orchard}}(n)$ of
$3$-point lines (lines containing exactly three of the points) attainable by a configuration
of $n$ points in the plane.

Burr, Grünbaum and Sloane [BGS74] constructed, for every $n \geq 3$, configurations of $n$
points with $\lfloor n(n-3)/6 \rfloor + 1$ three-point lines. Green and Tao [GT13] proved that
for all sufficiently large $n$ no configuration of $n$ points has more than this many
three-point lines, so $t_3^{\text{orchard}}(n) = \lfloor n(n-3)/6 \rfloor + 1$ for all
sufficiently large $n$. The exact value for every $n$ is not known: the formula fails for some
small $n$ (for example $t_3^{\text{orchard}}(7) = 6$), and the threshold in the Green–Tao
theorem is not explicit.

*References:*
- [Wikipedia, Orchard-planting problem](https://en.wikipedia.org/wiki/Orchard-planting_problem)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [BGS74] Burr, S. A., Grünbaum, B., Sloane, N. J. A., *The orchard problem*.
  Geometriae Dedicata 2 (1974), 397–424.
- [GT13] Green, B., Tao, T., *On sets defining few ordinary lines*.
  Discrete Comput. Geom. 50 (2013), 409–468. [arXiv:1208.4714](https://arxiv.org/abs/1208.4714)
- [A003035](https://oeis.org/A003035)
-/

open EuclideanGeometry Filter

namespace OrchardPlantingProblem

/-- A line in the plane: an affine subspace whose direction is one-dimensional. -/
def IsLine (L : AffineSubspace ℝ ℝ²) : Prop :=
  Module.finrank ℝ L.direction = 1

/-- The number of lines in the plane that contain exactly `k` points of the finite set `P`. -/
noncomputable def kPointLines (P : Finset ℝ²) (k : ℕ) : ℕ :=
  {L : AffineSubspace ℝ ℝ² | IsLine L ∧ ((P : Set ℝ²) ∩ L).ncard = k}.ncard

/--
$t_3^{\text{orchard}}(n)$: the maximum number of $3$-point lines attainable by a configuration
of $n$ points in the plane. Two distinct points lie on exactly one line, so this number is at
most $\binom{n}{2} / 3$ and the supremum is attained.
-/
noncomputable def orchardNumber (n : ℕ) : ℕ :=
  sSup {kPointLines P 3 | (P : Finset ℝ²) (_ : P.card = n)}

/--
For all sufficiently large $n$, the maximum number of $3$-point lines attainable by a
configuration of $n$ points in the plane is exactly $\lfloor n(n-3)/6 \rfloor + 1$: Green and
Tao [GT13] proved that there is $n_0$ such that for $n \geq n_0$ every configuration of $n$
points in the plane has at most $\lfloor n(n-3)/6 \rfloor + 1$ three-point lines, and this
matches the lower bound given by the constructions of Burr, Grünbaum and Sloane [BGS74].
-/
theorem orchard_planting_problem.variants.eventually :
    ∀ᶠ n : ℕ in atTop, orchardNumber n = n * (n - 3) / 6 + 1 := by
  sorry

end OrchardPlantingProblem

theorem OrchardPlantingProblem.orchard_planting_problem.variants.eventually.disproof : ¬ (type_of% @OrchardPlantingProblem.orchard_planting_problem.variants.eventually) := sorry
