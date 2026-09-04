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
# Quadrisecants of wild knots

A *quadrisecant* of a curve in $\mathbb{R}^3$ is a straight line that meets the curve in
(at least) four distinct points. A *knot* is a subset of $\mathbb{R}^3$ that is the image of a
topological embedding of the circle. Following Kuperberg, a knot is *tame* if some
homeomorphism of $\mathbb{R}^3$ carries it onto a polygonal (equivalently, piecewise linear or
smooth) knot, and *wild* otherwise.

It has been conjectured that every wild knot has infinitely many quadrisecants.
Kuperberg's original conjecture is stated for wild arcs; the Wikipedia list states it for
wild knots, and this is the version formalised here.

*References:*
- [Wikipedia, Quadrisecant](https://en.wikipedia.org/wiki/Quadrisecant)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Ku94] Kuperberg, G., *Quadrisecants of knots and links*. J. Knot Theory Ramifications 3
  (1994), 41–50. [arXiv:math/9712205](https://arxiv.org/abs/math/9712205)
-/

open Topology
open scoped EuclideanGeometry

namespace QuadrisecantsOfWildKnots

/-- A (topological) *knot* in `ℝ³`: a subset that is the image of a topological embedding of the
circle. -/
def IsKnot (K : Set ℝ³) : Prop :=
  ∃ γ : Circle → ℝ³, IsEmbedding γ ∧ Set.range γ = K

/-- A *polygonal knot* in `ℝ³`: a knot that is a closed polygon, i.e. the union of the closed
segments `[v i, v (i + 1)]` over a finite cyclic sequence of vertices `v`. -/
def IsPolygonalKnot (P : Set ℝ³) : Prop :=
  IsKnot P ∧ ∃ (n : ℕ) (v : Fin (n + 1) → ℝ³), P = ⋃ i, segment ℝ (v i) (v (i + 1))

/-- A knot `K ⊆ ℝ³` is *tame* if some homeomorphism of `ℝ³` carries it onto a polygonal knot
(Kuperberg's definition, [Ku94]). -/
def IsTameKnot (K : Set ℝ³) : Prop :=
  IsKnot K ∧ ∃ h : ℝ³ ≃ₜ ℝ³, IsPolygonalKnot (h '' K)

/-- A knot `K ⊆ ℝ³` is *wild* if it is not tame. -/
def IsWildKnot (K : Set ℝ³) : Prop :=
  IsKnot K ∧ ¬ IsTameKnot K

/-- A line `ℓ` in `ℝ³` (an affine subspace with one-dimensional direction) is a *quadrisecant* of
a set `K ⊆ ℝ³` if it meets `K` in at least four distinct points. -/
def IsQuadrisecant (K : Set ℝ³) (ℓ : AffineSubspace ℝ ℝ³) : Prop :=
  Module.finrank ℝ ℓ.direction = 1 ∧ 4 ≤ (K ∩ ℓ).encard

/-- A tame knot is a knot. -/
@[category API, AMS 51 57]
lemma IsTameKnot.isKnot {K : Set ℝ³} (hK : IsTameKnot K) : IsKnot K :=
  hK.1

/-- A wild knot is a knot. -/
@[category API, AMS 51 57]
lemma IsWildKnot.isKnot {K : Set ℝ³} (hK : IsWildKnot K) : IsKnot K :=
  hK.1

/-- A polygonal knot is tame (take the identity homeomorphism). -/
@[category API, AMS 51 57]
lemma IsPolygonalKnot.isTameKnot {P : Set ℝ³} (hP : IsPolygonalKnot P) : IsTameKnot P :=
  ⟨hP.1, Homeomorph.refl ℝ³, by simpa using hP⟩

/-- A knot is either tame or wild, and not both. -/
@[category API, AMS 51 57]
lemma isTameKnot_xor_isWildKnot {K : Set ℝ³} (hK : IsKnot K) :
    Xor' (IsTameKnot K) (IsWildKnot K) := by
  by_cases h : IsTameKnot K
  · exact Or.inl ⟨h, fun h' => h'.2 h⟩
  · exact Or.inr ⟨⟨hK, h⟩, h⟩

/--
**Quadrisecants of wild knots.**
Every wild knot $K \subseteq \mathbb{R}^3$ (a topological embedding of the circle that is not
carried to a polygonal knot by any homeomorphism of $\mathbb{R}^3$) has infinitely many
quadrisecants, i.e. infinitely many distinct straight lines each meeting $K$ in at least four
distinct points.
-/
@[category research open, AMS 51 57]
theorem quadrisecants_of_wild_knots (K : Set ℝ³) (hK : IsWildKnot K) :
    {ℓ : AffineSubspace ℝ ℝ³ | IsQuadrisecant K ℓ}.Infinite := by
  sorry

end QuadrisecantsOfWildKnots
