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
# Ropelength problems

The *ropelength* of a curve $C$ in $\mathbb{R}^3$ is $\operatorname{Len}(C)/\tau(C)$, the
quotient of its length by its *thickness* $\tau(C)$, the radius of the largest embedded normal
tube around $C$. The ropelength of a knot or link type is the minimal ropelength over all
curves of that type.

Following Cantarella, Kusner and Sullivan (after Gonzalez and Maddocks), the thickness of a
set $L \subseteq \mathbb{R}^3$ is the infimum of the circumradius $r(x, y, z)$ over all
triples of distinct points of $L$, where $r(x, y, z) = \infty$ for collinear triples. Every
curve of positive thickness is $C^{1,1}$, so no regularity needs to be imposed on the curves
over which the infimum is taken.

Thickness is measured as a *radius* (the Hopf link has ropelength $8\pi$), as in
Cantarella–Kusner–Sullivan and in the Wikipedia article.

This file states two open problems from the Wikipedia article:

* the ropelength of a nontrivial knot is bounded by a constant multiple of its crossing number;
* the ropelength of the Borromean rings is $58.006$.

*References:*
* [Wikipedia, Ropelength](https://en.wikipedia.org/wiki/Ropelength)
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* J. Cantarella, R. B. Kusner, J. M. Sullivan, *On the minimum ropelength of knots and links*,
  Invent. Math. 150 (2002), [arXiv:math/0103224](https://arxiv.org/abs/math/0103224)
* J. Cantarella, J. H. G. Fu, R. B. Kusner, J. M. Sullivan, N. C. Wrinkle, *Criticality for the
  Gehring link problem*, Geom. Topol. 10 (2006),
  [arXiv:math/0402212](https://arxiv.org/abs/math/0402212)
* Y. Diao, C. Ernst, A. Por, U. Ziegler, *The ropelengths of knots are almost linear in terms of
  their crossing numbers*, J. Knot Theory Ramifications 28 (2019),
  [doi:10.1142/S0218216519500858](https://doi.org/10.1142/S0218216519500858)
* T. Ashton, J. Cantarella, M. Piatek, E. Rawdon, *Knot tightening by constrained gradient
  descent*, Exp. Math. 20 (2011), [arXiv:1002.1723](https://arxiv.org/abs/1002.1723)
-/

open MeasureTheory Topology
open scoped EuclideanGeometry ContDiff ENNReal NNReal

namespace RopelengthProblems

/- ### Knots, links and ambient isotopy -/

/-- Two subsets `A`, `B` of `ℝ³` are *ambient isotopic* if there is a continuous family
`H t`, `t ∈ [0, 1]`, of homeomorphisms of `ℝ³` with `H 0 = id` and `H 1 '' A = B`.
Knot and link types are ambient isotopy classes. -/
def AmbientIsotopic (A B : Set ℝ³) : Prop :=
  ∃ H : unitInterval → (ℝ³ ≃ₜ ℝ³),
    Continuous (fun p : unitInterval × ℝ³ => H p.1 p.2) ∧
      H 0 = Homeomorph.refl ℝ³ ∧ H 1 '' A = B

/-- Ambient isotopy is reflexive: the constant family of identity maps is an ambient isotopy. -/
@[category API, AMS 57]
theorem AmbientIsotopic.refl (A : Set ℝ³) : AmbientIsotopic A A :=
  ⟨fun _ => Homeomorph.refl ℝ³, continuous_snd, rfl, Set.image_id A⟩

/-- A subset of `ℝ³` is a *knot* if it is the image of a topological embedding of the circle. -/
def IsKnot (K : Set ℝ³) : Prop :=
  ∃ γ : Circle → ℝ³, IsEmbedding γ ∧ Set.range γ = K

/-- The round unit circle in the plane `z = 0`, a representative of the unknot. -/
def unknot : Set ℝ³ :=
  {p | p 0 ^ 2 + p 1 ^ 2 = 1 ∧ p 2 = 0}

/-- The `i`-th component of the standard configuration of the Borromean rings: an ellipse with
semi-axes `2` and `1` in a coordinate plane. Explicitly, the three components are
* `i = 0`: `{z = 0, x² / 4 + y² = 1}` (in the `xy`-plane, major axis along the `x`-axis),
* `i = 1`: `{x = 0, y² / 4 + z² = 1}` (in the `yz`-plane, major axis along the `y`-axis),
* `i = 2`: `{y = 0, z² / 4 + x² = 1}` (in the `zx`-plane, major axis along the `z`-axis). -/
def borromeanComponent (i : Fin 3) : Set ℝ³ :=
  {x | x (i + 2) = 0 ∧ x i ^ 2 / 4 + x (i + 1) ^ 2 = 1}

/-- The standard configuration of the **Borromean rings**: three mutually perpendicular ellipses
with semi-axes `2` and `1`, one in each coordinate plane, with their major axes arranged
cyclically so that each ellipse passes through the disc spanned by the next one, see
`RopelengthProblems.borromeanComponent`. This is the ellipse version of the realization of the
Borromean rings by the three golden rectangles of a regular icosahedron. -/
def borromeanRings : Set ℝ³ := ⋃ i, borromeanComponent i

/-- The three components of `borromeanRings` are pairwise disjoint, so it is a link. -/
@[category test, AMS 57]
theorem pairwise_disjoint_borromeanComponent :
    Pairwise fun i j => Disjoint (borromeanComponent i) (borromeanComponent j) := by
  intro i j hij
  rw [Set.disjoint_left]
  rintro x ⟨hi, hi'⟩ ⟨hj, hj'⟩
  fin_cases i <;> fin_cases j <;> simp only [Fin.isValue, Fin.reduceAdd, Fin.zero_eta,
    Fin.mk_one, Fin.reduceFinMk, ne_eq, not_true_eq_false] at hij hi hi' hj hj' <;>
    rw [hi] at hj' <;> rw [hj] at hi' <;> nlinarith

/- ### Thickness and ropelength -/

/-- The *thickness* of a set `L ⊆ ℝ³` (Gonzalez–Maddocks, Cantarella–Kusner–Sullivan):
the infimum, over all triples of distinct points `x y z ∈ L`, of the radius of the circle
through `x`, `y`, `z`. Collinear triples have circumradius `∞` and hence do not contribute to
the infimum, so it suffices to range over affinely independent triples.

For a `C^{1,1}` link this is the radius of the largest embedded normal tube around `L`, and a
curve of positive thickness is automatically `C^{1,1}`. -/
noncomputable def thickness (L : Set ℝ³) : ℝ≥0∞ :=
  ⨅ (x ∈ L) (y ∈ L) (z ∈ L) (h : AffineIndependent ℝ ![x, y, z]),
    ENNReal.ofReal (Affine.Simplex.circumradius (⟨![x, y, z], h⟩ : Affine.Simplex ℝ ℝ³ 2))

/-- The *ropelength* of a set `L ⊆ ℝ³`: its length (one-dimensional Hausdorff measure, which
for a link is the total length of its components) divided by its thickness. It is `∞` if `L`
has zero thickness (and positive length). -/
noncomputable def ropelength (L : Set ℝ³) : ℝ≥0∞ :=
  μH[1] L / thickness L

/-- The ropelength of the knot or link type of `L`: the infimum of the ropelength over all sets
ambient isotopic to `L`. For a tame link type this infimum is attained (Cantarella, Kusner,
Sullivan); for a wild one it is `∞`. -/
noncomputable def minRopelength (L : Set ℝ³) : ℝ≥0∞ :=
  ⨅ (L' : Set ℝ³) (_ : AmbientIsotopic L L'), ropelength L'

@[category API, AMS 57]
theorem minRopelength_le {L L' : Set ℝ³} (h : AmbientIsotopic L L') :
    minRopelength L ≤ ropelength L' :=
  iInf₂_le L' h

/- ### Crossing number -/

/-- Orthogonal projection of `ℝ³` onto the `xy`-plane. -/
def proj (x : ℝ³) : ℝ × ℝ :=
  (x 0, x 1)

/-- `γ : ℝ → ℝ³` is a *smooth knot parametrisation*: a smooth, `1`-periodic, regular curve
which is injective on a period. Its image is a smooth (in particular tame) knot. -/
structure IsSmoothKnotParam (γ : ℝ → ℝ³) : Prop where
  contDiff : ContDiff ℝ ∞ γ
  periodic : Function.Periodic γ 1
  injOn : Set.InjOn γ (Set.Ico 0 1)
  deriv_ne_zero : ∀ t, deriv γ t ≠ 0

/-- The *crossings* of the projection of `γ` to the `xy`-plane: the points of the plane with at
least two preimages on the curve. -/
def crossings (γ : ℝ → ℝ³) : Set (ℝ × ℝ) :=
  {q | 2 ≤ (Set.range γ ∩ proj ⁻¹' {q}).encard}

/-- The projection of `γ` to the `xy`-plane is *regular*: the projected curve is an immersion,
it has only finitely many multiple points, every multiple point is a double point (exactly two
preimages on the curve), and at every double point the two strands cross transversally. -/
structure IsRegularProjection (γ : ℝ → ℝ³) : Prop where
  immersion : ∀ t, proj (deriv γ t) ≠ 0
  finite : (crossings γ).Finite
  encard_le_two : ∀ q, (Set.range γ ∩ proj ⁻¹' {q}).encard ≤ 2
  transverse : ∀ s t, γ s ≠ γ t → proj (γ s) = proj (γ t) →
    LinearIndependent ℝ ![proj (deriv γ s), proj (deriv γ t)]

/-- The *crossing number* of the knot type of `K`: the minimal number of crossings in a knot
diagram of `K`, i.e. in a regular projection to the `xy`-plane of a smooth knot ambient isotopic
to `K`. Every direction of projection is covered, since rotations are ambient isotopies. The
value is `⊤` if `K` has no smooth representative (e.g. for a wild knot). -/
noncomputable def crossingNumber (K : Set ℝ³) : ℕ∞ :=
  ⨅ (γ : ℝ → ℝ³) (_ : IsSmoothKnotParam γ) (_ : AmbientIsotopic K (Set.range γ))
    (_ : IsRegularProjection γ), (crossings γ).encard

@[category API, AMS 57]
theorem crossingNumber_le {K : Set ℝ³} {γ : ℝ → ℝ³} (hγ : IsSmoothKnotParam γ)
    (hK : AmbientIsotopic K (Set.range γ)) (hp : IsRegularProjection γ) :
    crossingNumber K ≤ (crossings γ).encard :=
  iInf₂_le_of_le γ hγ <| iInf₂_le hK hp

/- ### The problems -/

/--
**Linear ropelength bound.** For every knot $K$ the ropelength $L(K)$ satisfies
$L(K) = O(\operatorname{Cr}(K) \log^5 \operatorname{Cr}(K))$ (Diao, Ernst, Por, Ziegler), and
there are knot families with $L(K) = \Theta(\operatorname{Cr}(K))$. No knot family with
super-linear dependence of ropelength on crossing number has been observed, and it is conjectured
that the tight upper bound is linear: there is a constant $c > 0$ such that
$L(K) \le c \cdot \operatorname{Cr}(K)$ for every nontrivial (tame) knot $K$.

The unknot has crossing number $0$ but positive ropelength ($2\pi$), so it must be excluded.
For a wild knot both the crossing number and the ropelength are infinite, so the inequality
holds trivially and the statement is really about tame knots.
-/
@[category research open, AMS 51 57]
theorem ropelength_problems.parts.i :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ K : Set ℝ³, IsKnot K → ¬ AmbientIsotopic K unknot →
      minRopelength K ≤ c * (crossingNumber K : ℝ≥0∞) := by
  sorry

/--
**Ropelength of the Borromean rings.** The ropelength of the Borromean rings is conjectured to be
$58.006$: Cantarella, Fu, Kusner, Sullivan and Wrinkle constructed a ropelength-critical
configuration from parametrised arcs (three planar "guitar-shaped" components), with ropelength
approximately $58.0060$ in units where the thickness is the radius of the tube, and it is
conjectured to be the minimiser. Since $58.006$ is a rounded figure, the statement asserts that
the minimum ropelength agrees with $58.006$ to three decimal places, i.e. lies in
$[58.0055, 58.0065]$.
-/
@[category research open, AMS 51 57]
theorem ropelength_problems.parts.ii :
    minRopelength borromeanRings ∈ Set.Icc (ENNReal.ofReal 58.0055) (ENNReal.ofReal 58.0065) := by
  sorry

end RopelengthProblems
