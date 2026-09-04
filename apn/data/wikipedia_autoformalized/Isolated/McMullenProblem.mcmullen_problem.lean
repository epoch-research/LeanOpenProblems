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
# McMullen problem

Larman [La72], crediting a private communication of Peter McMullen, posed the following problem:
determine the largest number $\nu(d)$ such that any $\nu(d)$ points in general position in affine
$d$-space $\mathbb{R}^d$ can be mapped into convex position (so that they form the vertices of a
convex polytope) by a permissible projective transformation.

Here a finite point set is in *general position* if no $d + 1$ of its points lie on a common
hyperplane, a projective transformation of $\mathbb{R}^d$ is the map induced on the affine chart
$\{(x, 1)\}$ by an invertible linear map of $\mathbb{R}^{d + 1}$ (homogeneous coordinates), and
such a transformation is *permissible* for a point set if it sends none of the points to the
hyperplane at infinity.

Larman proved $2d + 1 \le \nu(d) \le (d + 1)^2$, and the conjectured answer is $\nu(d) = 2d + 1$.
This is known for $d = 2, 3, 4$.

*References:*
- [Wikipedia, McMullen problem](https://en.wikipedia.org/wiki/McMullen_problem)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [La72] Larman, D. G., *On sets projectively equivalent to the vertices of a convex polytope*,
  Bull. London Math. Soc. 4 (1972), 6–12.
-/

open scoped EuclideanGeometry

namespace McMullenProblem

variable {d : ℕ}

/--
The projective transformation of $\mathbb{R}^d$ induced by a linear automorphism `g` of the
homogeneous coordinate space $\mathbb{R}^d \times \mathbb{R} \cong \mathbb{R}^{d + 1}$, evaluated
at `x`: lift `x` to `(x, 1)`, apply `g`, and dehomogenise. In block form
$g = \begin{pmatrix} A & b \\ c^{\mathsf T} & \delta \end{pmatrix}$ this is
$x \mapsto (Ax + b) / (\langle c, x \rangle + \delta)$. The value is only meaningful when the last
homogeneous coordinate `(g (x, 1)).2` is nonzero, i.e. when `x` is not sent to the hyperplane at
infinity; see `McMullenProblem.IsPermissible`.
-/
noncomputable def projectiveMap (g : (ℝ^d × ℝ) ≃ₗ[ℝ] (ℝ^d × ℝ)) (x : ℝ^d) :
    ℝ^d :=
  (g (x, 1)).2⁻¹ • (g (x, 1)).1

/--
The projective transformation induced by `g` is *permissible* for the finite point set `S` if it
sends no point of `S` to the hyperplane at infinity, i.e. it is defined at every point of `S`.
-/
def IsPermissible (g : (ℝ^d × ℝ) ≃ₗ[ℝ] (ℝ^d × ℝ)) (S : Finset (ℝ^d)) : Prop :=
  ∀ x ∈ S, (g (x, 1)).2 ≠ 0

/--
A finite set `S` of points of $\mathbb{R}^d$ is in *general position* if any at most `d + 1` of
its points are affinely independent. For sets with at least `d + 1` points this says exactly that
no `d + 1` of the points lie on a common hyperplane.
-/
def InGeneralPosition (S : Finset (ℝ^d)) : Prop :=
  ∀ T ⊆ S, T.card ≤ d + 1 → AffineIndependent ℝ ((↑) : T → ℝ^d)

/--
A finite set `S` of points of $\mathbb{R}^d$ *can be projectively transformed into convex
position* if some projective transformation of $\mathbb{R}^d$ that is permissible for `S` maps
the points of `S` into convex position, i.e. every image point is a vertex of the convex hull of
the image points (`ConvexIndependent`).
-/
def IsProjectivelyConvexifiable (S : Finset (ℝ^d)) : Prop :=
  ∃ g : (ℝ^d × ℝ) ≃ₗ[ℝ] (ℝ^d × ℝ),
    IsPermissible g S ∧ ConvexIndependent ℝ fun x : S => projectiveMap g x

/--
`CanBeMadeConvex d n` says that every set of `n` points in general position in $\mathbb{R}^d$
can be mapped into convex position by a permissible projective transformation. The number
$\nu(d)$ of the McMullen problem is the largest `n` with this property.
-/
def CanBeMadeConvex (d n : ℕ) : Prop :=
  ∀ S : Finset (ℝ^d), S.card = n → InGeneralPosition S → IsProjectivelyConvexifiable S

/--
**The McMullen problem.** Let $\nu(d)$ be the largest number such that any $\nu(d)$ points in
general position in $\mathbb{R}^d$ (no $d + 1$ of them on a common hyperplane) can be mapped into
convex position (so that they form the vertices of a convex polytope) by a permissible projective
transformation (one sending none of the points to the hyperplane at infinity). The conjecture is
that $\nu(d) = 2d + 1$ for every $d \geq 2$, i.e. $2d + 1$ is the largest `n` such that
`CanBeMadeConvex d n` holds.

The restriction $d \geq 2$ is needed: on the line at most two points can be in convex position,
so $\nu(1) = 2$.
-/
theorem mcmullen_problem (d : ℕ) (hd : 2 ≤ d) :
    IsGreatest {n | CanBeMadeConvex d n} (2 * d + 1) := by
  sorry

end McMullenProblem

theorem McMullenProblem.mcmullen_problem.disproof : ¬ (type_of% @McMullenProblem.mcmullen_problem) := sorry
