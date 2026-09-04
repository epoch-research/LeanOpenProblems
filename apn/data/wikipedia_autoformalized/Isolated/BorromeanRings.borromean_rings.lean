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
# Borromean rings

The Borromean rings are the three-component link `L6a4`: three simple closed curves in
$\mathbb{R}^3$ that are linked, but such that any two of them are unlinked. Here they are
modelled by the standard realization as three mutually perpendicular ellipses.

A classical theorem (Lindström–Zetterström, and Freedman–Skora for arbitrary Brunnian links) says
that the Borromean rings cannot be formed from three round circles. In the other direction,
Matthew Cook conjectured that *any* three unknotted simple closed curves in $\mathbb{R}^3$ that
are not all circles can be arranged, by rigid motions of the individual components without
scaling, to form the Borromean rings. Howards proved this for polygonal unknots when scaling is
allowed (and, without scaling, when at least two of the polygons are planar), but also stated the
opposite conjecture, based on a candidate counterexample suggested by Jason Cantarella.

The Wikipedia list of unsolved problems asks:
*are there three unknotted space curves, not all three circles, which cannot be arranged to form
this link?*

*References:*
- [Wikipedia, Borromean rings](https://en.wikipedia.org/wiki/Borromean_rings)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [H. N. Howards, *Forming the Borromean rings out of arbitrary polygonal unknots*,
  arXiv:1406.3370](https://arxiv.org/abs/1406.3370)
- B. Lindström, H.-O. Zetterström, *Borromean circles are impossible*,
  Amer. Math. Monthly 98 (1991), 340–341.
- M. H. Freedman, R. Skora, *Strange actions of groups on spheres*,
  J. Differential Geom. 25 (1987), 75–98.
-/

open scoped EuclideanGeometry unitInterval

namespace BorromeanRings

/-- Two subsets `A`, `B` of `ℝ³` are **ambient isotopic** if there is a continuous family
`H t` (`t ∈ [0, 1]`) of homeomorphisms of `ℝ³` that starts at the identity and whose final
homeomorphism `H 1` maps `A` onto `B`. -/
def AmbientIsotopic (A B : Set ℝ³) : Prop :=
  ∃ H : I → ℝ³ ≃ₜ ℝ³,
    Continuous (fun p : I × ℝ³ => H p.1 p.2) ∧ H 0 = Homeomorph.refl ℝ³ ∧ H 1 '' A = B

/-- A subset `K` of `ℝ³` is a **round circle** if it is the set of points of some plane at a
fixed positive distance `r` from a centre `c` lying in that plane. The plane is described by the
centre `c` and a nonzero normal vector `n`. -/
def IsRoundCircle (K : Set ℝ³) : Prop :=
  ∃ (c n : ℝ³) (r : ℝ), n ≠ 0 ∧ 0 < r ∧ K = {x | dist x c = r ∧ inner ℝ (x - c) n = 0}

/-- A subset `K` of `ℝ³` is an **unknotted space curve** (an unknot) if it is ambient isotopic to
a round circle. Such a set is automatically a tame simple closed curve, i.e. the image of a
topological embedding of the circle. -/
def IsUnknot (K : Set ℝ³) : Prop :=
  ∃ C, IsRoundCircle C ∧ AmbientIsotopic K C

/-- The ellipse $x^2 / 4 + y^2 = 1$ in the plane $z = 0$. -/
def ellipse₁ : Set ℝ³ := {p | p 0 ^ 2 / 4 + p 1 ^ 2 = 1 ∧ p 2 = 0}

/-- The ellipse $y^2 / 4 + z^2 = 1$ in the plane $x = 0$. -/
def ellipse₂ : Set ℝ³ := {p | p 1 ^ 2 / 4 + p 2 ^ 2 = 1 ∧ p 0 = 0}

/-- The ellipse $z^2 / 4 + x^2 = 1$ in the plane $y = 0$. -/
def ellipse₃ : Set ℝ³ := {p | p 2 ^ 2 / 4 + p 0 ^ 2 = 1 ∧ p 1 = 0}

/-- The standard **Borromean rings**: the union of the three mutually perpendicular ellipses
`ellipse₁`, `ellipse₂`, `ellipse₃`, each with semi-axes `2` and `1`. The short axis of each
ellipse pierces the flat disk bounded by the next one (`ellipse₁` pierces the disk of `ellipse₂`
at $(0, \pm 1, 0)$, `ellipse₂` pierces the disk of `ellipse₃` at $(0, 0, \pm 1)$, and `ellipse₃`
pierces the disk of `ellipse₁` at $(\pm 1, 0, 0)$), while the long axis of each ellipse misses
the disk of the previous one. This is the configuration of the three golden rectangles inscribed
in a regular icosahedron, and it is the link `L6a4` (Alexander–Briggs `6³₂`). -/
def borromeanRings : Set ℝ³ := ellipse₁ ∪ ellipse₂ ∪ ellipse₃

/-- Three subsets `K₁`, `K₂`, `K₃` of `ℝ³` **form the Borromean rings** if they are pairwise
disjoint and their union is ambient isotopic to the standard Borromean rings `borromeanRings`. -/
def FormBorromeanRings (K₁ K₂ K₃ : Set ℝ³) : Prop :=
  Disjoint K₁ K₂ ∧ Disjoint K₂ K₃ ∧ Disjoint K₁ K₃ ∧
    AmbientIsotopic (K₁ ∪ K₂ ∪ K₃) borromeanRings

/--
**Borromean rings from arbitrary unknots.**
Are there three unknotted space curves $K_1, K_2, K_3 \subseteq \mathbb{R}^3$, not all three
round circles, which cannot be arranged to form the Borromean rings?

Here "arranged" means that each curve $K_i$ is moved individually by a rigid motion of
$\mathbb{R}^3$, i.e. a Euclidean isometry $\sigma_i$ (a composition of translations, rotations
and reflections), without any scaling. The moved curves $\sigma_1(K_1), \sigma_2(K_2),
\sigma_3(K_3)$ form the Borromean rings when they are pairwise disjoint and their union is
ambient isotopic to the standard Borromean rings. The three curves need not be distinct or
congruent.

A positive answer is the conjecture of Howards (arXiv:1406.3370, Section 3, based on a candidate
counterexample of Cantarella); a negative answer is the conjecture of Matthew Cook
(arXiv:1406.3370, Conjecture 1.1) that any three unknotted simple closed curves in space, not all
circles, can be combined without scaling to form the Borromean rings. Howards notes that allowing
scaling of the components could change the answer; scaling is not allowed here.
-/
theorem borromean_rings :
    ∃ K₁ K₂ K₃ : Set ℝ³, IsUnknot K₁ ∧ IsUnknot K₂ ∧ IsUnknot K₃ ∧
      ¬ (IsRoundCircle K₁ ∧ IsRoundCircle K₂ ∧ IsRoundCircle K₃) ∧
      ¬ ∃ σ₁ σ₂ σ₃ : ℝ³ ≃ᵃⁱ[ℝ] ℝ³, FormBorromeanRings (σ₁ '' K₁) (σ₂ '' K₂) (σ₃ '' K₃) := by
  sorry

end BorromeanRings

theorem BorromeanRings.borromean_rings.disproof : ¬ (type_of% @BorromeanRings.borromean_rings) := sorry
