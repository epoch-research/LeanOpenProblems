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
# Erdős–Oler conjecture

Packing $n$ unit circles in an equilateral triangle asks for the smallest side length of an
equilateral triangle that contains $n$ unit circles with pairwise disjoint interiors.
The Erdős–Oler conjecture states that if $n$ is a triangular number, then the smallest such
side length for $n - 1$ circles is the same as for $n$ circles.

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Circle packing in an equilateral triangle](https://en.wikipedia.org/wiki/Circle_packing_in_an_equilateral_triangle)
- Oler, Norman (1961), ["A finite packing problem"](https://doi.org/10.4153/CMB-1961-018-7),
  Canadian Mathematical Bulletin, 4 (2): 153–155
- Melissen, Hans (1993),
  ["Densest packings of congruent circles in an equilateral triangle"](https://doi.org/10.2307/2324212),
  The American Mathematical Monthly, 100 (10): 916–925
-/

open EuclideanGeometry

open scoped NNReal

namespace ErdosOlerConjecture

/--
The closed equilateral triangle of side length `s` with vertices $(0, 0)$, $(s, 0)$ and
$(s / 2, s \sqrt{3} / 2)$.

The side length is a nonnegative real, so that `equilateralTriangle s` is always the equilateral
triangle of side length $s$. Every equilateral triangle of side length $s$ in the plane is
congruent to this one, so fixing it loses no generality when packing circles into it.
-/
noncomputable def equilateralTriangle (s : ℝ≥0) : Set ℝ² :=
  convexHull ℝ {!₂[0, 0], !₂[(s : ℝ), 0], !₂[(s : ℝ) / 2, s * √3 / 2]}

/--
The set of side lengths `s` such that `n` unit circles can be packed in the equilateral triangle
of side length `s`: there are `n` centres such that each closed unit disc lies in the triangle,
and the open unit discs are pairwise disjoint (so the circles may touch but not overlap).
-/
def packableSides (n : ℕ) : Set ℝ≥0 :=
  {s | ∃ c : Fin n → ℝ², (∀ i, Metric.closedBall (c i) 1 ⊆ equilateralTriangle s) ∧
    Pairwise fun i j ↦ Disjoint (Metric.ball (c i) 1) (Metric.ball (c j) 1)}

/-- The three vertices of `equilateralTriangle s` are pairwise at distance `s`. -/
@[category test, AMS 51]
theorem dist_vertices (s : ℝ≥0) :
    dist (!₂[0, 0] : ℝ²) !₂[(s : ℝ), 0] = s ∧
      dist (!₂[0, 0] : ℝ²) !₂[(s : ℝ) / 2, s * √3 / 2] = s ∧
      dist (!₂[(s : ℝ), 0] : ℝ²) !₂[(s : ℝ) / 2, s * √3 / 2] = s := by
  have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [EuclideanSpace.dist_eq, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.dist_eq, sq_abs]
  refine ⟨?_, ?_, ?_⟩
  all_goals rw [Real.sqrt_eq_iff_eq_sq (by positivity) s.coe_nonneg]; ring_nf
  all_goals try (rw [h3]; ring)

/-- Zero circles can be packed in an equilateral triangle of any side length. -/
@[category test, AMS 52]
theorem packableSides_zero : packableSides 0 = Set.univ := by
  ext s
  simp [packableSides]

/--
**The Erdős–Oler conjecture.**
If $n$ is a triangular number, then packing $n - 1$ unit circles in an equilateral triangle
requires a triangle of the same size as packing $n$ unit circles: the least side length of an
equilateral triangle in which $n - 1$ unit circles can be packed equals the least side length
of an equilateral triangle in which $n$ unit circles can be packed. Formally, there is one side
length `s` that is the least element of both sets of admissible side lengths.

Here $n = k(k + 1) / 2$ with $k \ge 2$: for $k = 1$ (that is, $n = 1$) the statement would
compare packing one circle with packing no circles at all, which is degenerate.
-/
@[category research open, AMS 52]
theorem erdos_oler_conjecture (n k : ℕ) (hk : 2 ≤ k) (hn : n = k * (k + 1) / 2) :
    ∃ s, IsLeast (packableSides (n - 1)) s ∧ IsLeast (packableSides n) s := by
  sorry

end ErdosOlerConjecture
