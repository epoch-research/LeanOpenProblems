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
# Rectilinear crossing number and halving lines

A *rectilinear drawing* of the complete graph $K_n$ is given by a set $S$ of $n$ points in
general position in the plane (no three collinear); its edges are the straight line segments
joining the points of $S$. The number of crossings of this drawing is denoted $\overline{cr}(S)$,
and the *rectilinear crossing number* $\overline{cr}(n)$ of $K_n$ is the minimum of
$\overline{cr}(S)$ over all such $S$.

A *halving line* of $S$ is a line which passes through two points of $S$ and equally bisects the
remaining points.

Conjecture: for each arrangement of points in which $\overline{cr}(n)$ is minimized, the number
of halving lines is maximized. The converse is known to be false.

*References:*
* [Wikipedia, Crossing number (graph theory)](https://en.wikipedia.org/wiki/crossing_number_%28graph_theory%29)
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [Rectilinear Crossing Number project](http://www.ist.tugraz.at/staff/aichholzer/research/rp/triangulations/crossing/)
-/

open EuclideanGeometry Finset

namespace CrossingNumber

/-- The number of crossings $\overline{cr}(S)$ of the rectilinear drawing of the complete graph
on the point set `S`: the number of unordered pairs of edges `s(a, b)`, `s(c, d)` with four
distinct endpoints in `S` whose interiors (open segments) meet. -/
noncomputable def crossings (S : Finset ℝ²) : ℕ :=
  {e : Sym2 (Sym2 ℝ²) | ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S,
    e = s(s(a, b), s(c, d)) ∧ ({a, b, c, d} : Finset ℝ²).card = 4 ∧
      (openSegment ℝ a b ∩ openSegment ℝ c d).Nonempty}.ncard

/-- The line `ℓ` is a *halving line* of `S`: it passes through two distinct points `a, b` of `S`,
and the two open half-planes bounded by `ℓ` contain the same number of points of `S`.
The side of `ℓ` on which a point `p` lies is recorded by the sign of the oriented angle
`∡ a b p`, which is `0` exactly when `p` lies on `ℓ`.

For `S` in general position (no three collinear) the only points of `S` on `ℓ` are `a` and `b`,
so `ℓ` equally bisects the remaining `#S - 2` points. -/
def IsHalvingLine (S : Finset ℝ²) (ℓ : AffineSubspace ℝ ℝ²) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ℓ = line[ℝ, a, b] ∧
    #{p ∈ S | (∡ a b p).sign = 1} = #{p ∈ S | (∡ a b p).sign = -1}

/-- The number of halving lines of the point set `S`. -/
noncomputable def halvingLines (S : Finset ℝ²) : ℕ :=
  {ℓ | IsHalvingLine S ℓ}.ncard

/--
For each arrangement of points in which the rectilinear crossing number is minimized, is the
number of halving lines maximized?

Precisely: let $S$ be a set of $n$ points in general position (no three collinear) in the plane
such that $\overline{cr}(S) = \overline{cr}(n)$, i.e. the straight-line drawing of $K_n$ on $S$
has the minimum number of crossings among all $n$-point sets in general position. Is the number
of halving lines of $S$ then the maximum number of halving lines of an $n$-point set in general
position?

The question is asked for every $n$. For odd $n$ no line through two points of a set in general
position equally bisects the remaining $n - 2$ points, so the statement is trivially true in that
case; the content of the conjecture is for even $n$.
-/
theorem crossing_number : 
    ∀ S : Finset ℝ², NonTrilinear (S : Set ℝ²) →
      (∀ T : Finset ℝ², #T = #S → NonTrilinear (T : Set ℝ²) →
        crossings S ≤ crossings T) →
      ∀ T : Finset ℝ², #T = #S → NonTrilinear (T : Set ℝ²) →
        halvingLines T ≤ halvingLines S := by
  sorry

end CrossingNumber

theorem CrossingNumber.crossing_number.disproof : ¬ (type_of% @CrossingNumber.crossing_number) := sorry
