/-
Copyright 2025 The Formal Conjectures Authors.

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
# Some conjectures about ranks of elliptic curves over ℚ

*References:*
- [PPVW2016] Jennifer Park, Bjorn Poonen, John Voight, and Melanie Matchett Wood.
    A heuristic for boundedness of ranks of elliptic curves,
    https://ems.press/journals/jems/articles/16228
- [BS2013] Manjul Bhargava and Arul Shankar. The average size of the 5-Selmer group of
   elliptic curves is 6, and the average rank is less than 1, https://arxiv.org/pdf/1312.7859
- [Goldfeld1979] Dorian Goldfeld. Conjectures on elliptic curves over quadratic fields,
   Number Theory Carbondale 1979, Lecture Notes in Math. 751, 108-118,
   https://doi.org/10.1007/BFb0062705
- [Smith2025] Alexander Smith. The Birch and Swinnerton-Dyer conjecture implies Goldfeld's
   conjecture, https://arxiv.org/abs/2503.17619
- [Wikipedia](https://en.wikipedia.org/wiki/Rank_of_an_elliptic_curve)
- [ICARM](https://elliptic-rank.icarm.cloud/curve/273)
- [Stoll] Michael Stoll. EllipticCurves, a Lean 4 formalization of the Mordell–Weil theorem
   and explicit 2-descent, https://github.com/MichaelStollBayreuth/EllipticCurves
-/

namespace EllipticCurveRank

open EllipticCurveRank

/-- A data structure representing isomoprhism classes of elliptic curves over ℚ.
Every elliptic curve over ℚ is isomorphic to one with Weierstrass equation `y² = x³ + Ax + B`,
and the pair `(A,B)` is unique if it satisfy the `reduced` condition below.
See Section 5.1 in [PPVW2016]. -/
structure RatEllipticCurve : Type where
  A : ℤ
  B : ℤ
  reduced (p : ℕ) : p.Prime → ¬ ((p ^ 4 : ℤ) ∣ A ∧ (p ^ 6 : ℤ) ∣ B)
  Δ_ne_zero : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0

open Module (finrank)
open WeierstrassCurve

namespace RatEllipticCurve

/-- Convert the structure `RatEllipticCurve` to a Weierstrass curve. -/
def toWeierstrass (E : RatEllipticCurve) : Affine ℚ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := E.A, a₆ := E.B }

/-- The rank of an elliptic curve over ℚ. -/
noncomputable abbrev rank (E : RatEllipticCurve) : ℕ := finrank ℤ E.toWeierstrass.Point

open WeierstrassCurve in
instance (E : RatEllipticCurve) : E.toWeierstrass.IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr <| by
    convert mul_ne_zero (show (-16 : ℚ) ≠ 0 by norm_num) (Int.cast_ne_zero.mpr E.Δ_ne_zero)
    simp_rw [toWeierstrass, Δ, b₂, b₄, b₆, Int.cast_add, Int.cast_mul, Int.cast_pow]
    ring

/-- The naïve height of an elliptic curve over ℚ. -/
def naiveHeight (E : RatEllipticCurve) : ℕ := max (4 * E.A.natAbs ^ 3) (27 * E.B.natAbs ^ 2)

/-- The set of elliptic curves over ℚ with naïve height less than or equal to a given height. -/
def heightLE (H : ℕ) : Set RatEllipticCurve := {E : RatEllipticCurve | E.naiveHeight ≤ H}

open scoped Topology
open Filter (atTop)

/-- The quadratic twist $E^d$ of $E : y^2 = x^3 + Ax + B$ by an integer $d$, given by the
Weierstrass equation $y^2 = x^3 + d^2Ax + d^3B$. For $d \neq 0$ this is the twist of $E$
corresponding to the quadratic field $\mathbb{Q}(\sqrt{d})$. See Section 1 of [Smith2025]. -/
def quadraticTwist (E : RatEllipticCurve) (d : ℤ) : Affine ℚ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := d ^ 2 * E.A, a₆ := d ^ 3 * E.B }

/-- The rank of the quadratic twist $E^d$ of an elliptic curve $E$ over $\mathbb{Q}$. -/
noncomputable abbrev twistRank (E : RatEllipticCurve) (d : ℤ) : ℕ :=
  finrank ℤ (E.quadraticTwist d).Point

/-- The set of nonzero integers $d$ with $|d| \leq H$, which index the quadratic twists $E^d$
ordered by $|d|$. By `naiveHeight_quadraticTwist` this is the same as ordering them by height. -/
def twistIndexLE (H : ℕ) : Set ℤ := {d : ℤ | d ≠ 0 ∧ |d| ≤ (H : ℤ)}

/-- [PPVW2016] 8.2(c): the number of elliptic curves over ℚ with rank ≥ 21 and naïve height
at most `H` is asymptotically at most `H ^ o(1)`. -/
theorem twentyone_le_rank_height_count_asymptotic :
    ∃ f : ℕ → ℝ, atTop.Tendsto f (𝓝 0) ∧
      ∀ H : ℕ, 1 < H → {E ∈ heightLE H | 21 ≤ E.rank}.ncard ≤ (H : ℝ) ^ f H := by
  sorry

end RatEllipticCurve

namespace WeierstrassCurve

/-  See https://en.wikipedia.org/wiki/Rank_of_an_elliptic_curve#Largest_known_ranks -/

/-- The elliptic curve over ℚ of rank at least 31 found by Claude, Levent Alpöge and
Ava Howell in 2026. It has rank exactly 31 assuming the generalized Riemann hypothesis and
Birch and Swinnerton-Dyer conjecture. -/
def claudeAlpogeHowell31 : Affine ℚ where
  a₁ := 1
  a₂ := 1
  a₃ := 1
  a₄ := -1284727764113567728281797636015784768866707681415849262157224232063
  a₆ := 560368321454261339256859338901915312332769858684945406858043869199456710681989058863306170127006181

/-- See https://elliptic-rank.icarm.cloud/curve/302.
User profile: https://elliptic-rank.icarm.cloud/user/18
        and   https://elliptic-rank.icarm.cloud/user/53
-/
theorem Δ_claudeAlpogeHowell31 : claudeAlpogeHowell31.Δ =
    2 ^ 15 * 3 ^ 4 * 5 ^ 4 * 7 ^ 6 * 11 ^ 4 * 13 ^ 5 * 19 ^ 2 * 23 ^ 2 * 29 ^ 3 * 37 ^ 2 * 41 ^ 2 *
    73 ^ 2 * 131 ^ 2 * 167 ^ 2 * 7547 * 632881 * 966509 * 18145679437533309132469 *
    767028866604834801397681553 *
    30580600452196904409276223329355584892025407195996968868775951126238056443210297 := by
  rw [claudeAlpogeHowell31, Δ, b₂, b₄, b₆, b₈]; norm_num

instance : claudeAlpogeHowell31.IsElliptic where
  isUnit := by rw [Δ_claudeAlpogeHowell31]; norm_num

/-- The elliptic curve over ℚ of rank at least 30 found by user `ranksunbounded` in 2026.
User profile: https://elliptic-rank.icarm.cloud/user/18
It has rank exactly 30 assuming the generalized Riemann hypothesis and Birch and Swinnerton-Dyer
conjecture. -/
def ranksunbounded30 : Affine ℚ where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := -201769035260418549083594900060734240952308696994802735114305555
  a₆ := 1151107939141058565733479426024323225135665982951300586808823640527729578307228357301072889377

/-- See https://elliptic-rank.icarm.cloud/curve/273. -/
theorem Δ_ranksunbounded30 : ranksunbounded30.Δ =
    -2 ^ 16 * 3 ^ 12 * 5 ^ 8 * 7 ^ 5 * 13 ^ 5 * 31 ^ 2 * 41 ^ 2 * 47 ^ 4 * 53 ^ 3 * 67 ^ 3 * 379 ^ 2 *
    4349 * 25721454817 *
    97018222656318846556561979214040553412450110580812087282349817173780902099339117104673990259247421230916714670243202937 := by
  rw [ranksunbounded30, Δ, b₂, b₄, b₆, b₈]; norm_num

instance : ranksunbounded30.IsElliptic where
  isUnit := by rw [Δ_ranksunbounded30]; norm_num

/-- The elliptic curve over ℚ of rank at least 29 found by Elkies and Klagsbrun in 2024.
It has rank exactly 29 assuming the generalized Riemann hypothesis. -/
def elkiesKlagsbrun29 : Affine ℚ where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := -27006183241630922218434652145297453784768054621836357954737385
  a₆ := 55258058551342376475736699591118191821521067032535079608372404779149413277716173425636721497

/-- See https://mathoverflow.net/a/478050. -/
theorem Δ_elkiesKlagsbrun29 : elkiesKlagsbrun29.Δ =
    -2 ^ 19 * 3 ^ 7 * 5 ^ 7 * 7 ^ 4 * 11 ^ 5 * 13 ^ 3 * 17 ^ 4 * 31 ^ 3 * 41 ^ 2 * 43 ^ 2 * 61 ^ 2 *
    233 * 241 ^ 2 * 4139 * 678146849364709860535420504397393 *
    159788990966780131363155786084695062643236502969 *
    4402149008473369392540402625019227412319473055901 := by
  rw [elkiesKlagsbrun29, Δ, b₂, b₄, b₆, b₈]; norm_num

instance elkiesKlagsbrun29IsElliptic : elkiesKlagsbrun29.IsElliptic where
  isUnit := by rw [Δ_elkiesKlagsbrun29]; norm_num

/-- The elliptic curve over ℚ of rank at least 28 found by Elkies in 2006.
It has rank exactly 28 assuming the generalized Riemann hypothesis. -/
def elkies28 : Affine ℚ where
  a₁ := 1
  a₂ := -1
  a₃ := 1
  a₄ := -20067762415575526585033208209338542750930230312178956502
  a₆ := 34481611795030556467032985690390720374855944359319180361266008296291939448732243429

/-- See https://mathoverflow.net/a/478050. -/
theorem Δ_elkies28 : elkies28.Δ =
    2 ^ 15 * 3 ^ 6 * 5 ^ 6 * 7 ^ 4 * 11 ^ 2 * 13 ^ 4 * 17 ^ 5 * 19 ^ 3 *
    48463 * 20650099 * 315574902691581877528345013999136728634663121 *
    376018840263193489397987439236873583997122096511452343225772113000611087671413 := by
  rw [elkies28, Δ, b₂, b₄, b₆, b₈]; norm_num

instance elkies28IsElliptic : elkies28.IsElliptic where
  isUnit := by rw [Δ_elkies28]; norm_num

-- TODO: compute the rank of some rank 0 / 1 curve.

end WeierstrassCurve

end EllipticCurveRank

theorem EllipticCurveRank.RatEllipticCurve.twentyone_le_rank_height_count_asymptotic.disproof : ¬ (type_of% @EllipticCurveRank.RatEllipticCurve.twentyone_le_rank_height_count_asymptotic) := sorry
