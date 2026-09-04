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
# Outer billiards

Outer billiards is a dynamical system defined relative to a convex shape $P$ in the plane.
For a point $x$ outside $P$, the outer billiards map sends $x$ to the point $y$ such that the
segment from $x$ to $y$ is tangent to $P$ at its midpoint and $P$ lies to the right of the ray
from $x$ to $y$. Equivalently, $y$ is the reflection of $x$ through the point where the right
support line from $x$ touches $P$. When $P$ is a polygon, the map is undefined at the points $x$
whose right support line meets $P$ along a side. The (two-sided) orbit of a point $x$ is the
sequence obtained by iterating the map and its inverse; it is well defined when every iterate is
defined, which is the case for almost every point.

An orbit is *bounded* if it is contained in some bounded region of the plane, and *unbounded*
otherwise. An orbit is *periodic* if it eventually repeats. Since the outer billiards map is
injective where it is defined, a well-defined orbit eventually repeats if and only if it is
periodic in the usual sense.

The Wikipedia list of unsolved problems in mathematics records "many problems concerning an
outer billiard, for example showing that outer billiards relative to almost every convex polygon
have unbounded orbits". This file states this problem and the second open problem from the
open-problems section of the Wikipedia article on outer billiards: outer billiards relative to a
regular polygon has almost every orbit periodic.

*References:*
- [Wikipedia, *Outer billiard*, Open questions](https://en.wikipedia.org/wiki/Outer_billiard%23open_problems)
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [R. E. Schwartz, *Unbounded orbits for outer billiards I*](https://arxiv.org/abs/math/0702073)
- [S. Tabachnikov, *A proof of Culter's theorem on existence of periodic orbits in polygonal outer billiards*](https://arxiv.org/abs/0706.1003)
-/

open EuclideanGeometry MeasureTheory
open scoped Real

namespace OuterBilliard

/--
The points of `P` lying on the right support line from `x`: the points `v ∈ P` such that
all of `P` lies (weakly) to the right of the ray from `x` through `v`.

Here "to the right" is measured with the standard orientation of the plane: `p` lies to the right
of the ray from `x` through `v` when the signed area `areaForm (v - x) (p - x)` is nonpositive.
-/
def rightSupportPoints (P : Set ℝ²) (x : ℝ²) : Set ℝ² :=
  {v ∈ P | ∀ p ∈ P, positiveOrientation.areaForm (v - x) (p - x) ≤ 0}

/--
`IsStep P x y` means that `y` is the image of `x` under the outer billiards map relative to `P`:
`x` lies outside `P`, the right support line from `x` touches `P` in exactly one point `v`, and
`y` is the reflection of `x` through `v`. When the right support line from `x` meets `P` along a
segment, the outer billiards map is undefined at `x` and `IsStep P x y` fails for every `y`.
-/
def IsStep (P : Set ℝ²) (x y : ℝ²) : Prop :=
  x ∉ P ∧ ∃ v, rightSupportPoints P x = {v} ∧ y = Equiv.pointReflection v x

/--
`IsOrbit P o` means that the two-sided sequence `o : ℤ → ℝ²` is a well-defined outer
billiards orbit relative to `P`: for every `k`, the point `o (k + 1)` is the image of `o k`
under the outer billiards map. Such an orbit is determined by any one of its points.
-/
def IsOrbit (P : Set ℝ²) (o : ℤ → ℝ²) : Prop :=
  ∀ k, IsStep P (o k) (o (k + 1))

/--
The closed regular `n`-gon with center `c`, circumradius `r` and rotation angle `θ`: the convex
hull of the points `c + r • (cos (θ + 2πk/n), sin (θ + 2πk/n))` for `k = 0, …, n - 1`.
Every regular `n`-gon in the plane is of this form for some `c`, some `r > 0` and some `θ`.
-/
noncomputable def regularPolygon (n : ℕ) (c : ℝ²) (r θ : ℝ) : Set ℝ² :=
  convexHull ℝ (Set.range fun k : Fin n =>
    c + r • !₂[Real.cos (θ + 2 * π * k / n), Real.sin (θ + 2 * π * k / n)])

/--
**Unbounded orbits for almost every convex polygon.**
Outer billiards relative to almost every convex polygon has unbounded orbits.

Precisely: for every $n \ge 4$ and Lebesgue almost every $n$-tuple of points
$(p_0, \dots, p_{n-1}) \in (\mathbb{R}^2)^n$ that are the vertices, in cyclic order, of a
(strictly) convex $n$-gon $P$, there is a point outside $P$ whose outer billiards orbit relative
to $P$ is well defined and unbounded, i.e. not contained in any bounded region of the plane.

Triangles are excluded: every triangle is affinely equivalent to a rational polygon, so all
outer billiards orbits relative to a triangle are periodic (Vivaldi–Shaidenko, Kołodziej,
Gutkin–Simanyi), and the claim for $n = 3$ is false. Since the outer billiards map is equivariant
under affine maps of the plane, the choice of parametrisation of convex $n$-gons by their vertex
tuples does not affect the meaning of "almost every".

Schwartz proved that outer billiards relative to any irrational kite (in particular the Penrose
kite) has unbounded orbits; kites form a null set of quadrilaterals, so the problem is open.
-/
theorem outer_billiard.parts.i (n : ℕ) (hn : 4 ≤ n) :
    ∀ᵐ p : Fin n → ℝ², IsConvexPolygon p →
      ∃ o, IsOrbit (convexHull ℝ (Set.range p)) o ∧ ¬ Bornology.IsBounded (Set.range o) := by
  sorry

end OuterBilliard

theorem OuterBilliard.outer_billiard.parts.i.disproof : ¬ (type_of% @OuterBilliard.outer_billiard.parts.i) := sorry
