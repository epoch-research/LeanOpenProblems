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
# Covering problem of Rado

Let $S$ be a finite family of squares in the plane with sides parallel to the coordinate axes
and whose union has area $1$. A subfamily $I$ of $S$ is *independent* if its squares are pairwise
disjoint, which we read as having pairwise disjoint interiors (squares may share boundary points;
this reading does not change the constant below). Tibor Radó (1928) asked how small the largest
area covered by an independent subfamily of $S$ can be, i.e. for the value of
$$F(\text{square}) = \inf_S \sup_I |I|,$$
where $S$ ranges over such families, $I$ over the independent subfamilies of $S$ and $|I|$ is the
area covered by $I$.

Radó proved $F(\text{square}) \geq 1/9$ and conjectured $F(\text{square}) = 1/4$. The conjecture
holds for families of congruent squares (Sokolin, R. Rado, Zalgaller), but Ajtai (1973) disproved
it in general with a family for which every independent subfamily covers at most $1/4 - 1/1728$ of
the total area. The best known bounds are $1/8.4797 \leq F(\text{square}) \leq 1/4 - 1/384$
(Bereg, Dumitrescu, Jiang). The exact value of $F(\text{square})$ is open.

*References:*
- [Wikipedia, Covering problem of Rado](https://en.wikipedia.org/wiki/covering_problem_of_Rado)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Ra28] Radó, T., _Sur un problème relatif à un théorème de Vitali_,
  Fundamenta Mathematicae 11 (1928), 228–229.
- [Aj73] Ajtai, M., _The solution of a problem of T. Radó_,
  Bull. Acad. Polon. Sci. Sér. Sci. Math. Astronom. Phys. 21 (1973), 61–63.
- [BDJ10] Bereg, S., Dumitrescu, A., Jiang, M., _On covering problems of Rado_,
  Algorithmica 57 (2010), 538–561.
  [doi:10.1007/s00453-009-9298-z](https://doi.org/10.1007/s00453-009-9298-z)
-/

open MeasureTheory
open scoped EuclideanGeometry ENNReal

namespace CoveringProblemOfRado

/--
The closed axis-parallel square $[a_0, a_0 + s] \times [a_1, a_1 + s]$ with lower-left corner `a`
and side length `s`.
-/
def axisParallelSquare (a : ℝ²) (s : ℝ) : Set ℝ² :=
  {p | ∀ i, p i ∈ Set.Icc (a i) (a i + s)}

/-- A set `Q` is an *axis-parallel square* if it is a closed square with sides parallel to the
coordinate axes and positive side length. -/
def IsAxisParallelSquare (Q : Set ℝ²) : Prop :=
  ∃ (a : ℝ²) (s : ℝ), 0 < s ∧ Q = axisParallelSquare a s

/-- A finite family of sets is a *square family* if each of its members is an axis-parallel
square. -/
def IsSquareFamily (S : Finset (Set ℝ²)) : Prop :=
  ∀ Q ∈ S, IsAxisParallelSquare Q

/-- A finite family of sets is *independent* if its members have pairwise disjoint interiors.
For squares this means that no two of them overlap, though they may share boundary points. -/
def IsIndependent (I : Finset (Set ℝ²)) : Prop :=
  (I : Set (Set ℝ²)).PairwiseDisjoint interior

/-- The largest area covered by an independent subfamily of the finite family `S`.
Since `S` has finitely many subfamilies, this supremum is a maximum. -/
noncomputable def maxIndependentArea (S : Finset (Set ℝ²)) : ℝ≥0∞ :=
  ⨆ (I : Finset (Set ℝ²)) (_ : I ⊆ S) (_ : IsIndependent I), volume (⋃ Q ∈ I, Q)

/--
The set of values of `maxIndependentArea S`, where `S` ranges over the finite families of
axis-parallel squares whose union has area $1$. Its infimum is Radó's constant $F(\text{square})$.
-/
def radoValues : Set ℝ≥0∞ :=
  {maxIndependentArea S | (S : Finset (Set ℝ²)) (_ : IsSquareFamily S)
    (_ : volume (⋃ Q ∈ S, Q) = 1)}

/--
Radó [Ra28] proved that every finite family of axis-parallel squares whose union has area $1$
contains an independent subfamily covering area at least $1/9$.
-/
theorem covering_problem_of_rado.variants.rado_lower_bound : 1 / 9 ∈ lowerBounds radoValues := by
  sorry

end CoveringProblemOfRado

theorem CoveringProblemOfRado.covering_problem_of_rado.variants.rado_lower_bound.disproof : ¬ (type_of% @CoveringProblemOfRado.covering_problem_of_rado.variants.rado_lower_bound) := sorry
