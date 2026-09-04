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
# Triangular billiards

A point mass (or light ray) moves inside a triangle along straight segments and reflects off
the sides with angle of incidence equal to angle of reflection. If it reaches a vertex, it is
extinguished. A *periodic billiards path* is a trajectory that returns to its starting position
and orientation after finitely many reflections. The open problem asks whether every triangle
admits such a path. A 2026 preprint by G. Forni claims a positive answer for all polygons.

*References:*
- [Wikipedia, Triangular billiards](https://en.wikipedia.org/wiki/Triangular_billiards)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Forni, *Existence of a Periodic Orbit for Billiards in Polygons*, arXiv:2606.10102](https://arxiv.org/abs/2606.10102)
-/

open scoped EuclideanGeometry Real

namespace TriangularBilliards

/--
A periodic billiards path in the triangle `T` with `n` reflections, given by its bounce points
`p 0, p 1, …, p (n - 1)` in cyclic order, where the bounce point `p i` lies on the side of `T`
opposite the vertex `T.points (s i)`. The conditions are:
- each bounce point lies strictly inside a side, so the path never hits a vertex;
- consecutive bounce points lie on different sides, so each segment of the path crosses the
  interior of the triangle (and the path does not slide along a side);
- at each bounce point the angle of incidence equals the angle of reflection.

Since the indices are taken cyclically, the reflection law at `p 0` involves `p (n - 1)`, so
the trajectory closes up with the same position and orientation as it started with.
-/
structure IsPeriodicBilliardPath (T : Affine.Triangle ℝ ℝ²) {n : ℕ} [NeZero n]
    (p : Fin n → ℝ²) (s : Fin n → Fin 3) : Prop where
  /-- `p i` lies strictly between the two endpoints of the side opposite `T.points (s i)`. -/
  sbtw : ∀ i, Sbtw ℝ (T.points (s i + 1)) (p i) (T.points (s i + 2))
  /-- Consecutive bounce points lie on different sides. -/
  side_ne : ∀ i, s i ≠ s (i + 1)
  /-- Angle of incidence equals angle of reflection: the angle between the incoming segment and
  one endpoint of the side equals the angle between the outgoing segment and the other
  endpoint. -/
  angle_eq : ∀ i,
    ∠ (p (i - 1)) (p i) (T.points (s i + 1)) = ∠ (p (i + 1)) (p i) (T.points (s i + 2))

/-- The triangle `T` has a periodic billiards path. -/
def HasPeriodicBilliardPath (T : Affine.Triangle ℝ ℝ²) : Prop :=
  ∃ (n : ℕ) (_ : NeZero n) (p : Fin n → ℝ²) (s : Fin n → Fin 3),
    IsPeriodicBilliardPath T p s

/--
**Triangular billiards.** Does every triangle have a periodic billiards path?

Here a triangle is any nondegenerate triangle in the Euclidean plane, and a periodic billiards
path is a closed polygonal trajectory in the triangle that reflects off the sides with angle of
incidence equal to angle of reflection and never hits a vertex.
-/
theorem triangular_billiards :
    ∀ T : Affine.Triangle ℝ ℝ², HasPeriodicBilliardPath T := by
  sorry

/-- The right isosceles triangle with vertices `(0, 0)`, `(1, 0)` and `(0, 1)`. -/
def rightIsoscelesTriangle : Affine.Triangle ℝ ℝ² where
  points := ![!₂[0, 0], !₂[1, 0], !₂[0, 1]]
  independent := by
    rw [affineIndependent_iff_not_collinear_set, collinear_iff_of_mem (Set.mem_insert _ _)]
    rintro ⟨v, hv⟩
    obtain ⟨r, hr⟩ := hv !₂[1, 0] (by simp)
    obtain ⟨r', hr'⟩ := hv !₂[0, 1] (by simp)
    have h1 := congrArg (· 0) hr
    have h2 := congrArg (· 1) hr
    have h3 := congrArg (· 0) hr'
    have h4 := congrArg (· 1) hr'
    simp at h1 h2 h3 h4
    obtain rfl | h2 := h2 <;> obtain rfl | h3 := h3 <;> simp_all

end TriangularBilliards

theorem TriangularBilliards.triangular_billiards.disproof : ¬ (type_of% @TriangularBilliards.triangular_billiards) := sorry
