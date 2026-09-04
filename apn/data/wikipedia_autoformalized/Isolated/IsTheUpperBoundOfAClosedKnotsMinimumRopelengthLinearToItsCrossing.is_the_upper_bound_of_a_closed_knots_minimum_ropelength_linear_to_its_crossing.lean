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
# Is the minimum ropelength of a knot linear in its crossing number?

The *ropelength* of a closed curve $C$ in $\mathbb{R}^3$ is the scale-invariant ratio
$\operatorname{Len}(C)/\tau(C)$ of its length to its thickness. Following Gonzalez–Maddocks and
Cantarella–Kusner–Sullivan, the thickness $\tau(C)$ is the infimum of the radii of the circles
through three distinct points of $C$. It equals the radius of the largest embedded normal tube
around $C$. The ropelength $\operatorname{Rop}(K)$ of a knot type $K$ is the infimum of the
ropelength over all curves that realize $K$. The crossing number $\operatorname{Cr}(K)$ is the
least number of crossings in a regular projection of a curve that realizes $K$.

Diao, Ernst, Por and Ziegler proved
$\operatorname{Rop}(K) = O(\operatorname{Cr}(K) \log^5 \operatorname{Cr}(K))$.
The Wikipedia list of unsolved problems asks whether the upper bound is in fact linear:
is $\operatorname{Rop}(K) = O(\operatorname{Cr}(K))$?

The unknot has crossing number $0$ and ropelength $2\pi > 0$, so the linear bound must allow an
additive constant. Since every nontrivial knot has crossing number at least $3$, this is the same
as a purely linear bound for nontrivial knots. Ropelength is measured in units of the thickness
radius; measuring in diameters halves it and does not affect the question.

*References:*
- [Wikipedia, Ropelength](https://en.wikipedia.org/wiki/Ropelength)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [CKS02] Cantarella, J., Kusner, R. B., Sullivan, J. M., *On the minimum ropelength of knots and
  links*, Invent. Math. 150 (2002), 257–286. [arXiv:math/0103224](https://arxiv.org/abs/math/0103224)
- [DEPZ19] Diao, Y., Ernst, C., Por, A., Ziegler, U., *The ropelengths of knots are almost linear
  in terms of their crossing numbers*, J. Knot Theory Ramifications 28 (2019), 1950085.
-/

namespace IsTheUpperBoundOfAClosedKnotsMinimumRopelengthLinearToItsCrossing

open scoped EuclideanGeometry unitInterval ENNReal NNReal

/-- A (closed) knot: a $C^1$ closed curve in $\mathbb{R}^3$ with nowhere vanishing derivative,
parametrised by $\mathbb{R}$ with period `1` and injective on each period. -/
structure IsKnot (γ : ℝ → ℝ³) : Prop where
  periodic : Function.Periodic γ 1
  contDiff : ContDiff ℝ 1 γ
  deriv_ne_zero : ∀ t, deriv γ t ≠ 0
  injective : ∀ s t, γ s = γ t → ∃ n : ℤ, t = s + n

/-- Two closed curves are *ambient isotopic* (have the same knot type) if a continuous family of
homeomorphisms of $\mathbb{R}^3$ starting at the identity carries the image of the first onto the
image of the second. -/
def Isotopic (γ₀ γ₁ : ℝ → ℝ³) : Prop :=
  ∃ H : I → ℝ³ ≃ₜ ℝ³, Continuous (fun p : I × ℝ³ => H p.1 p.2) ∧
    H 0 = Homeomorph.refl ℝ³ ∧ H 1 '' Set.range γ₀ = Set.range γ₁

/-- The length of one period of the closed curve `γ`. -/
noncomputable def length (γ : ℝ → ℝ³) : ℝ := ∫ t in (0:ℝ)..1, ‖deriv γ t‖

/-- The *thickness* of the curve `γ` (Gonzalez–Maddocks, [CKS02, Section 2]): the infimum of the
circumradii of all non-degenerate triangles with vertices on the curve. Collinear triples of
points, which have infinite circumradius, do not contribute to the infimum. -/
noncomputable def thickness (γ : ℝ → ℝ³) : ℝ :=
  ⨅ s : {s : Affine.Simplex ℝ ℝ³ 2 // ∀ i, s.points i ∈ Set.range γ}, s.1.circumradius

/-- The *ropelength* of the curve `γ`: its length divided by its thickness, measured in units of
the thickness radius. It is `∞` when the thickness is `0`. -/
noncomputable def curveRopelength (γ : ℝ → ℝ³) : ℝ≥0∞ :=
  ENNReal.ofReal (length γ) / ENNReal.ofReal (thickness γ)

/-- The (minimum) *ropelength* of the knot type of `γ`: the infimum of the ropelength over all
knots ambient isotopic to `γ`. -/
noncomputable def ropelength (γ : ℝ → ℝ³) : ℝ≥0∞ :=
  ⨅ (γ' : ℝ → ℝ³) (_ : IsKnot γ') (_ : Isotopic γ γ'), curveRopelength γ'

/-- The orthogonal projection of $\mathbb{R}^3$ onto the plane orthogonal to `u`. -/
noncomputable def proj (u : ℝ³) : ℝ³ →L[ℝ] ℝ³ := (ℝ ∙ u)ᗮ.starProjection

/-- The *crossings* of the projection of `γ` along `u`: the unordered pairs of distinct parameters
in one period whose projections coincide, encoded as pairs `(s, t)` with `0 ≤ s < t < 1`. -/
def crossings (γ : ℝ → ℝ³) (u : ℝ³) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Ico 0 1 ∧ p.2 ∈ Set.Ico 0 1 ∧ p.1 < p.2 ∧
    proj u (γ p.1) = proj u (γ p.2)}

/-- The projection along the direction `u ≠ 0` is a *regular projection* of the knot `γ`: the
projected curve is regular (no tangent of `γ` is parallel to `u`), every point of the plane has
at most two preimages on the curve, the double points are transverse, and there are finitely many
of them. -/
structure IsRegularProjection (γ : ℝ → ℝ³) (u : ℝ³) : Prop where
  ne_zero : u ≠ 0
  deriv_ne_zero : ∀ t, proj u (deriv γ t) ≠ 0
  encard_le_two : ∀ y, {t ∈ Set.Ico (0:ℝ) 1 | proj u (γ t) = y}.encard ≤ 2
  transverse : ∀ p ∈ crossings γ u,
    LinearIndependent ℝ ![proj u (deriv γ p.1), proj u (deriv γ p.2)]
  finite : (crossings γ u).Finite

/-- The *crossing number* of the knot type of `γ`: the least number of crossings in a regular
projection of a knot ambient isotopic to `γ`. -/
noncomputable def crossingNumber (γ : ℝ → ℝ³) : ℕ∞ :=
  ⨅ (γ' : ℝ → ℝ³) (_ : IsKnot γ') (_ : Isotopic γ γ') (u : ℝ³)
    (_ : IsRegularProjection γ' u), (crossings γ' u).encard

/-- Is the minimum ropelength of a closed knot bounded above by a linear function of its crossing
number? That is, are there constants $a, b$ such that every knot type $K$ satisfies
$\operatorname{Rop}(K) \le a \operatorname{Cr}(K) + b$? -/
theorem is_the_upper_bound_of_a_closed_knots_minimum_ropelength_linear_to_its_crossing :
    ∃ a b : ℝ≥0, ∀ γ : ℝ → ℝ³, IsKnot γ →
      ropelength γ ≤ a * (crossingNumber γ : ℝ≥0∞) + b := by
  sorry

end IsTheUpperBoundOfAClosedKnotsMinimumRopelengthLinearToItsCrossing

theorem IsTheUpperBoundOfAClosedKnotsMinimumRopelengthLinearToItsCrossing.is_the_upper_bound_of_a_closed_knots_minimum_ropelength_linear_to_its_crossing.disproof : ¬ (type_of% @IsTheUpperBoundOfAClosedKnotsMinimumRopelengthLinearToItsCrossing.is_the_upper_bound_of_a_closed_knots_minimum_ropelength_linear_to_its_crossing) := sorry
