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
# Ropelength and crossing number: the constant in $L(K) \geq a \operatorname{Cr}(K)^{3/4}$

The *ropelength* of a closed curve $C \subseteq \mathbb{R}^3$ is $\operatorname{Len}(C) / \tau(C)$,
where $\operatorname{Len}(C)$ is its length and $\tau(C)$ is its *thickness*, the radius of the
largest embedded normal tube around $C$. The (minimum) ropelength $L(K)$ of a knot type $K$ is the
infimum of the ropelength over all curves realising $K$. Buck and Simon proved that
$L(K) \geq (4\pi/11)^{3/4} \operatorname{Cr}(K)^{3/4} \approx 1.105 \operatorname{Cr}(K)^{3/4}$
for every knot $K$, where $\operatorname{Cr}(K)$ is the crossing number. Computer tightenings of
torus knots suggest that the optimal constant cannot exceed $10.76$. Wikipedia's list of unsolved
problems asks:

"What constant $1.1 < a \leq 10.76$ governs the lower bound of a closed knot $K$'s minimum
ropelength $L(K) \geq a \operatorname{Cr}(K)^{3/4}$?"

Here a *knot* is a simple closed curve in $\mathbb{R}^3$, i.e. a topological embedding
`γ : Circle → ℝ³`, and two knots have the same *knot type* if their images are ambient
isotopic. Thickness is measured as a *radius* (as in Cantarella–Kusner–Sullivan and
Klotz–Maldonado), which is the convention in which the constants $1.1$ and $10.76$ are stated;
in this convention the round unit circle has ropelength $2\pi$.

*References:*
- [Wikipedia, Ropelength](https://en.wikipedia.org/wiki/Ropelength)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [BS99] Buck, G., Simon, J., *Thickness and crossing number of knots*, Topology Appl. 91 (1999),
  245–257.
- [CKS02] Cantarella, J., Kusner, R. B., Sullivan, J. M., *On the minimum ropelength of knots and
  links*, Invent. Math. 150 (2002), 257–286.
  [arXiv:math/0103224](https://arxiv.org/abs/math/0103224)
- [KM21] Klotz, A. R., Maldonado, M., *The ropelength of complex knots*, J. Phys. A 54 (2021).
  [arXiv:2108.01857](https://arxiv.org/abs/2108.01857)
- [KT25] Klotz, A. R., Thompson, F., *Ropelength-minimizing concentric helices and non-alternating
  torus knots*. [arXiv:2504.00861](https://arxiv.org/abs/2504.00861)
-/

namespace WhatConstant11ALeq1076GovernsTheLowerBoundOfAClosedKnotK

open Topology
open scoped EuclideanGeometry MeasureTheory ENNReal Real unitInterval

/-- Two subsets `K₁ K₂` of `ℝ³` are **ambient isotopic** if there is a continuous family
`H t`, `t ∈ [0, 1]`, of homeomorphisms of `ℝ³` with `H 0 = id` and `H 1 '' K₁ = K₂`. -/
def AmbientIsotopic (K₁ K₂ : Set ℝ³) : Prop :=
  ∃ H : I → ℝ³ ≃ₜ ℝ³, Continuous (fun p : I × ℝ³ => H p.1 p.2) ∧
    H 0 = Homeomorph.refl ℝ³ ∧ H 1 '' K₁ = K₂

/-- Every set is ambient isotopic to itself (via the constant isotopy). -/
@[category API, AMS 57]
theorem AmbientIsotopic.refl (K : Set ℝ³) : AmbientIsotopic K K :=
  ⟨fun _ => Homeomorph.refl ℝ³, continuous_snd, rfl, by simp⟩

/-- The **thickness** of a set `K ⊆ ℝ³`, following Gonzalez–Maddocks and [CKS02, §1]: the
infimum of the circumradii $r(x, y, z)$ over all triples of distinct points $x, y, z \in K$.
Collinear triples have $r = \infty$ and are omitted (they never contribute to the infimum). For a
`C¹` curve this equals the normal injectivity radius, i.e. the radius of the largest embedded
normal tube around the curve [CKS02, §1]; it is `0` for curves that are not `C^{1,1}`. -/
noncomputable def thickness (K : Set ℝ³) : ℝ :=
  sInf {r | ∃ s : Affine.Simplex ℝ ℝ³ 2, (∀ i, s.points i ∈ K) ∧ s.circumradius = r}

/-- The **ropelength** of a set `K ⊆ ℝ³` (the image of a closed curve): its length, i.e. its
one-dimensional Hausdorff measure `μH[1] K`, divided by its thickness. It is `∞` when the curve
has zero thickness (and positive length) or infinite length. -/
noncomputable def ropelength (K : Set ℝ³) : ℝ≥0∞ :=
  μH[1] K / ENNReal.ofReal (thickness K)

/-- The **minimum ropelength** of the knot type of the knot `γ`: the infimum of the ropelength
over all knots `γ'` whose image is ambient isotopic to that of `γ`. -/
noncomputable def minRopelength (γ : Circle → ℝ³) : ℝ≥0∞ :=
  ⨅ (γ' : Circle → ℝ³)
    (_ : IsEmbedding γ' ∧ AmbientIsotopic (Set.range γ) (Set.range γ')),
    ropelength (Set.range γ')

/-- The vertical projection `ℝ³ → ℝ × ℝ` onto the first two coordinates. -/
def planeProj (p : ℝ³) : ℝ × ℝ := (p 0, p 1)

/-- The `2π`-periodic parametrisation `t ↦ γ (Circle.exp t)` of a curve
`γ : Circle → ℝ³`. -/
noncomputable def periodicParam (γ : Circle → ℝ³) : ℝ → ℝ³ :=
  fun t => γ (Circle.exp t)

/-- The **crossings** of the vertical projection of `γ : Circle → ℝ³`: the points of the plane
with exactly two preimages on the curve. -/
def crossingSet (γ : Circle → ℝ³) : Set (ℝ × ℝ) :=
  {p | (Set.range γ ∩ planeProj ⁻¹' {p}).encard = 2}

/-- The curve `γ : Circle → ℝ³` is `C¹` and its vertical projection to the plane is a
**regular diagram**: the projected curve is an immersion, every point of the plane has at most
two preimages on the curve, there are finitely many double points, and at every double point
the two strands cross transversally. -/
structure IsRegularDiagram (γ : Circle → ℝ³) : Prop where
  contDiff : ContDiff ℝ 1 (periodicParam γ)
  immersion : ∀ t, deriv (planeProj ∘ periodicParam γ) t ≠ 0
  encard_le_two : ∀ p, (Set.range γ ∩ planeProj ⁻¹' {p}).encard ≤ 2
  finite : (crossingSet γ).Finite
  transverse : ∀ t₁ t₂, periodicParam γ t₁ ≠ periodicParam γ t₂ →
    planeProj (periodicParam γ t₁) = planeProj (periodicParam γ t₂) →
    LinearIndependent ℝ
      ![deriv (planeProj ∘ periodicParam γ) t₁, deriv (planeProj ∘ periodicParam γ) t₂]

/-- The **crossing number** of the knot type of the knot `γ`: the least number of crossings in a
regular diagram of a knot `γ'` whose image is ambient isotopic to that of `γ`. (Any regular
projection direction can be rotated to the vertical one by an ambient isotopy, so it suffices to
consider vertical projections.) For a knot type with no `C¹` representative (a wild knot) the set
below is empty and the value is `0`; such knot types have infinite ropelength. -/
noncomputable def crossingNumber (γ : Circle → ℝ³) : ℕ :=
  sInf {n | ∃ γ' : Circle → ℝ³,
    IsEmbedding γ' ∧ AmbientIsotopic (Set.range γ) (Set.range γ') ∧
    IsRegularDiagram γ' ∧ (crossingSet γ').ncard = n}

/-- The optimal constant `a` in the lower bound $L(K) \geq a \operatorname{Cr}(K)^{3/4}$: the
supremum of all `a : ℝ` such that `a * Cr(K) ^ (3/4) ≤ L(K)` holds for every knot type `K`,
where `L(K)` is the minimum ropelength and `Cr(K)` the crossing number of `K`. The unknot has
`Cr = 0` and imposes no constraint, so this is the infimum of $L(K) / \operatorname{Cr}(K)^{3/4}$
over all nontrivial knots. -/
noncomputable def ropelengthCrossingConstant : ℝ :=
  sSup {a : ℝ | ∀ γ : Circle → ℝ³, IsEmbedding γ →
    ENNReal.ofReal (a * (crossingNumber γ : ℝ) ^ (3 / 4 : ℝ)) ≤ minRopelength γ}

/-- The round unit circle in the plane $x_2 = 0$. -/
noncomputable def roundCircle : Circle → ℝ³ :=
  fun z => !₂[(z : ℂ).re, (z : ℂ).im, 0]

@[category test, AMS 51 57]
theorem isEmbedding_roundCircle : IsEmbedding roundCircle := by
  sorry

/-- Every non-degenerate triangle inscribed in the unit circle has circumradius `1`. -/
@[category test, AMS 51 57]
theorem thickness_range_roundCircle : thickness (Set.range roundCircle) = 1 := by
  sorry

/-- The round unit circle has length `2π` and thickness `1`, so its ropelength is `2π`. -/
@[category test, AMS 51 57]
theorem ropelength_range_roundCircle :
    ropelength (Set.range roundCircle) = ENNReal.ofReal (2 * π) := by
  sorry

/-- The vertical projection of the round circle is injective, so the unknot has crossing
number `0`. -/
@[category test, AMS 51 57]
theorem crossingNumber_roundCircle : crossingNumber roundCircle = 0 := by
  sorry

/--
**Ropelength versus crossing number.**
Let $a^*$ be the optimal constant such that every closed knot $K$ satisfies
$L(K) \geq a^* \operatorname{Cr}(K)^{3/4}$, where $L(K)$ is the minimum ropelength and
$\operatorname{Cr}(K)$ the crossing number of $K$. Then $1.1 < a^* \leq 10.76$.

The lower bound is the theorem of Buck and Simon [BS99] (see also [CKS02, §10]), which gives
$a^* \geq (4\pi/11)^{3/4} \approx 1.105$. The upper bound rests on computer tightenings of
$T(Q+1, Q)$ torus knots with at least $224$ crossings [KM21], [KT25], and is not proven.
-/
@[category research open, AMS 51 57]
theorem what_constant_1_1_a_leq_10_76_governs_the_lower_bound_of_a_closed_knot_k :
    1.1 < ropelengthCrossingConstant ∧ ropelengthCrossingConstant ≤ 10.76 := by
  sorry

/-- The lower half: the optimal constant exceeds $1.1$. This follows from the theorem of
Buck and Simon [BS99], since $(4\pi/11)^{3/4} > 1.1$. -/
@[category research solved, AMS 51 57]
theorem what_constant_1_1_a_leq_10_76_governs_the_lower_bound_of_a_closed_knot_k.variants.lower_bound :
    1.1 < ropelengthCrossingConstant := by
  sorry

/-- The theorem of Buck and Simon [BS99], as stated in [CKS02, §10]: every knot type $K$ satisfies
$L(K) \geq (4\pi \operatorname{Cr}(K) / 11)^{3/4}$; hence $a^* \geq (4\pi/11)^{3/4}$. -/
@[category research solved, AMS 51 57]
theorem what_constant_1_1_a_leq_10_76_governs_the_lower_bound_of_a_closed_knot_k.variants.buck_simon :
    (4 * π / 11) ^ (3 / 4 : ℝ) ≤ ropelengthCrossingConstant := by
  sorry

/-- The upper half: the optimal constant is at most $10.76$, i.e. for every $a > 10.76$ some
knot $K$ has $L(K) < a \operatorname{Cr}(K)^{3/4}$. This is supported by computer tightenings of
torus knots [KM21], [KT25], but is not proven. -/
@[category research open, AMS 51 57]
theorem what_constant_1_1_a_leq_10_76_governs_the_lower_bound_of_a_closed_knot_k.variants.upper_bound :
    ropelengthCrossingConstant ≤ 10.76 := by
  sorry

end WhatConstant11ALeq1076GovernsTheLowerBoundOfAClosedKnotK
