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

/-- An axis-parallel square of side length `s` has area $s^2$. -/
@[category API, AMS 52]
theorem volume_axisParallelSquare (a : ℝ²) {s : ℝ} (hs : 0 ≤ s) :
    volume (axisParallelSquare a s) = ENNReal.ofReal (s ^ 2) := by
  have h : axisParallelSquare a s =
      WithLp.ofLp ⁻¹' Set.Icc (WithLp.ofLp a) (WithLp.ofLp a + fun _ => s) := by
    ext p
    simp [axisParallelSquare, Set.mem_Icc, Pi.le_def, forall_and]
  rw [h, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  simp [sq, ENNReal.ofReal_mul hs]

/-- The largest area covered by an independent subfamily of a single set is its area. -/
@[category API, AMS 52]
theorem maxIndependentArea_singleton (Q : Set ℝ²) : maxIndependentArea {Q} = volume Q := by
  apply le_antisymm
  · refine iSup₂_le fun I hI => iSup_le fun _ => measure_mono ?_
    exact Set.iUnion₂_subset fun Q' hQ' => by
      rw [Finset.mem_singleton.mp (hI hQ')]
  · have h1 : IsIndependent {Q} := by simp [IsIndependent]
    have h2 : ({Q} : Finset (Set ℝ²)) ⊆ {Q} := Finset.Subset.refl _
    calc volume Q = volume (⋃ Q' ∈ ({Q} : Finset (Set ℝ²)), Q') := by simp
      _ ≤ _ := le_iSup₂_of_le (f := fun I (_ : I ⊆ {Q}) =>
          ⨆ (_ : IsIndependent I), volume (⋃ Q' ∈ I, Q')) {Q} h2 (le_iSup_of_le h1 le_rfl)

/-- The family consisting of the unit square alone has value $1$. In particular `radoValues` is
nonempty, so it has a unique greatest lower bound. -/
@[category test, AMS 52]
theorem one_mem_radoValues : 1 ∈ radoValues := by
  refine ⟨{axisParallelSquare 0 1}, fun Q hQ => ⟨0, 1, one_pos, Finset.mem_singleton.mp hQ⟩,
    ?_, ?_⟩
  · simp [volume_axisParallelSquare]
  · simp [maxIndependentArea_singleton, volume_axisParallelSquare]

/--
**The covering problem of Rado.**
If the union of finitely many axis-parallel squares has unit area, how small can the largest
area covered by a subfamily of pairwise disjoint squares be? That is, what is the greatest lower
bound $F(\text{square})$ of the largest area covered by an independent subfamily, taken over all
finite families of axis-parallel squares whose union has area $1$?

Here "disjoint" is read as having disjoint interiors, so squares of the subfamily may touch
along their boundaries. This does not change the value of $F(\text{square})$.
-/
@[category research open, AMS 52]
theorem covering_problem_of_rado : IsGLB radoValues answer(sorry) := by
  sorry

/--
**Radó's conjecture** [Ra28]: every finite family of axis-parallel squares whose union has area
$1$ contains an independent subfamily covering area at least $1/4$, and the constant $1/4$ cannot
be improved, i.e. $F(\text{square}) = 1/4$. This was disproved by Ajtai [Aj73].
-/
@[category research solved, AMS 52]
theorem covering_problem_of_rado.variants.rado_conjecture : ¬ IsGLB radoValues (1 / 4) := by
  sorry

/--
Radó [Ra28] proved that every finite family of axis-parallel squares whose union has area $1$
contains an independent subfamily covering area at least $1/9$.
-/
@[category research solved, AMS 52]
theorem covering_problem_of_rado.variants.rado_lower_bound : 1 / 9 ∈ lowerBounds radoValues := by
  sorry

/--
Ajtai [Aj73] disproved Radó's conjecture by constructing a finite family of axis-parallel squares
for which every independent subfamily covers at most $1/4 - 1/1728$ of the area of the union.
Hence $F(\text{square}) \leq 1/4 - 1/1728 = 431/1728$.
-/
@[category research solved, AMS 52]
theorem covering_problem_of_rado.variants.ajtai_upper_bound : sInf radoValues ≤ 431 / 1728 := by
  sorry

/--
Bereg, Dumitrescu and Jiang [BDJ10] proved that every finite family of axis-parallel squares whose
union has area $1$ contains an independent subfamily covering area at least $1/8.4797$.
-/
@[category research solved, AMS 52]
theorem covering_problem_of_rado.variants.bereg_dumitrescu_jiang_lower_bound :
    1 / 8.4797 ∈ lowerBounds radoValues := by
  sorry

/--
Bereg, Dumitrescu and Jiang [BDJ10] proved that $F(\text{square}) \leq 1/4 - 1/384 = 95/384$.
-/
@[category research solved, AMS 52]
theorem covering_problem_of_rado.variants.bereg_dumitrescu_jiang_upper_bound :
    sInf radoValues ≤ 95 / 384 := by
  sorry

/--
Radó's conjecture holds for families of congruent squares (Sokolin, R. Rado, Zalgaller): every
finite family of axis-parallel squares of a common side length whose union has area $1$ contains
an independent subfamily covering area at least $1/4$, and the constant $1/4$ cannot be improved.
-/
@[category research solved, AMS 52]
theorem covering_problem_of_rado.variants.congruent_squares :
    IsGLB {maxIndependentArea S | (S : Finset (Set ℝ²))
      (_ : ∃ s : ℝ, 0 < s ∧ ∀ Q ∈ S, ∃ a, Q = axisParallelSquare a s)
      (_ : volume (⋃ Q ∈ S, Q) = 1)} (1 / 4) := by
  sorry

end CoveringProblemOfRado
