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
# Disk covering problem

The disk covering problem asks for the smallest real number $r(n)$ such that $n$ disks of
radius $r(n)$ can be arranged in such a way as to cover the unit disk.

Disks are closed disks in the Euclidean plane. The set of radii $r$ for which $n$ closed disks
of radius $r$ can cover the closed unit disk is closed and bounded below, so the smallest such
radius exists and $r(n)$ is a minimum, which we express with `IsLeast`.

The values $r(1) = r(2) = 1$, $r(3) = \sqrt 3 / 2$ and $r(4) = \sqrt 2 / 2$ are elementary.
K. Bezdek (1983, 1984) determined $r(5)$, $r(6)$ and $r(7) = 1/2$, and G. Fejes Tóth (2005)
determined $r(8)$, $r(9)$ and $r(10)$. For $n = 11$ and $n = 12$ the values of $r(n)$ are not
known; the best coverings known have radii $0.380083\ldots$ and $0.361141\ldots$ respectively
(Wikipedia lists these radii truncated to six decimals).

*References:*
- [Wikipedia, Disk covering problem](https://en.wikipedia.org/wiki/disk_covering_problem)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Erich Friedman, Circles Covering Circles](https://erich-friedman.github.io/packing/circovcir/)
- R. Kershner, [The number of circles covering a set](https://doi.org/10.2307/2371320),
  American Journal of Mathematics 61 (1939), 665–671.
- K. Bezdek, Über einige Kreisüberdeckungen, Beiträge zur Algebra und Geometrie 14 (1983).
- K. Bezdek, Über einige optimale Konfigurationen von Kreisen, Annales Universitatis
  Scientiarum Budapestinensis de Rolando Eötvös Nominatae, Sectio Mathematica 27 (1984).
- G. Fejes Tóth, Thinnest covering of a circle by eight, nine, or ten congruent circles,
  Combinatorial and Computational Geometry, MSRI Publications 52 (2005).
-/

open EuclideanGeometry Real

namespace DiskCoveringProblem

/--
`CanCoverUnitDisk n r` means that `n` closed disks of radius `r` can be arranged so as to cover
the closed unit disk in the Euclidean plane: there are centres `c 0, …, c (n - 1)` with
$\overline{B}(0, 1) \subseteq \bigcup_i \overline{B}(c_i, r)$. Coincident centres are allowed.
It fails for every `r` when `n = 0`, and it fails for every negative `r`.
-/
def CanCoverUnitDisk (n : ℕ) (r : ℝ) : Prop :=
  ∃ c : Fin n → ℝ², Metric.closedBall 0 1 ⊆ ⋃ i, Metric.closedBall (c i) r

/--
The centres of the "central disk" layout of `k + 1` disks: one disk is centred at the origin
and the remaining `k` disks are placed symmetrically around it, at distance `d` from the origin
and at the equally spaced angles $2\pi j / k$, $j = 0, \dots, k - 1$.
-/
noncomputable def centralLayout (k : ℕ) (d : ℝ) : Fin (k + 1) → ℝ² :=
  Fin.cons 0 fun j => !₂[d * cos (2 * π * j / k), d * sin (2 * π * j / k)]

/--
The best covering of the unit disk by eleven equal disks known to date has radius
$0.380083\ldots$; in particular eleven disks of radius $0.380084$ cover the unit disk.
-/
theorem disk_covering_problem.variants.eleven_upper_bound : CanCoverUnitDisk 11 0.380084 := by
  sorry

end DiskCoveringProblem

theorem DiskCoveringProblem.disk_covering_problem.variants.eleven_upper_bound.disproof : ¬ (type_of% @DiskCoveringProblem.disk_covering_problem.variants.eleven_upper_bound) := sorry
