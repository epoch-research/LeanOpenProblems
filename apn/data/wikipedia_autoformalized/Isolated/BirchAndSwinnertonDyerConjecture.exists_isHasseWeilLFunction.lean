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
# Birch and Swinnerton-Dyer conjecture

Let $E$ be an elliptic curve over a number field $K$. By the Mordell–Weil theorem the abelian
group $E(K)$ of $K$-points is finitely generated, so it has a rank.

For a finite place $v$ of $K$ with residue field $\mathbb{F}_v$ of cardinality $q_v$, let
$\tilde{E}$ be the reduction modulo $v$ of a Weierstrass equation for $E$ that is minimal at $v$,
and put $a_v = q_v + 1 - \#\tilde{E}(\mathbb{F}_v)$, where $\#\tilde{E}(\mathbb{F}_v)$ counts all
$\mathbb{F}_v$-points of the reduced cubic, including the singular point when the reduction is
bad. Then $a_v$ is the trace of Frobenius at a place of good reduction and $a_v = 1, -1, 0$ at a
place of split multiplicative, non-split multiplicative or additive reduction respectively.
The Hasse–Weil $L$-function of $E$ is the Euler product
$$L(E, s) = \prod_{v \text{ good}} (1 - a_v q_v^{-s} + q_v^{1 - 2s})^{-1}
  \prod_{v \text{ bad}} (1 - a_v q_v^{-s})^{-1},$$
which converges absolutely for $\operatorname{Re}(s) > 3/2$. Hasse conjectured that $L(E, s)$
extends to an entire function. For $K = \mathbb{Q}$ this is a consequence of the modularity
theorem; for a general number field it is still open.

The **Birch and Swinnerton-Dyer conjecture** states that the rank of $E(K)$ equals the order of
vanishing of $L(E, s)$ at $s = 1$. The case $K = \mathbb{Q}$ is one of the seven Millennium Prize
Problems of the Clay Mathematics Institute.

The strong form of the conjecture, which predicts the leading Taylor coefficient of $L(E, s)$ at
$s = 1$ in terms of the Tate–Shafarevich group, the real period, the regulator, the Tamagawa
numbers and the torsion subgroup of $E$, is not stated here: Mathlib has none of these invariants.

*References:*
- [Wikipedia, *Birch and Swinnerton-Dyer conjecture*](https://en.wikipedia.org/wiki/Birch_and_Swinnerton-Dyer_conjecture)
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [A. Wiles, *The Birch and Swinnerton-Dyer conjecture*, Clay Mathematics Institute](https://www.claymath.org/wp-content/uploads/2022/05/birchswin.pdf)
- [J. H. Silverman, *The Arithmetic of Elliptic Curves*, Appendix C §16][silverman2009]
-/

namespace BirchAndSwinnertonDyerConjecture

open IsDedekindDomain NumberField WeierstrassCurve
open Module (finrank)
open scoped WeierstrassCurve.Affine

variable {K : Type*} [Field K] [NumberField K] (E : WeierstrassCurve K)
  (v : HeightOneSpectrum (𝓞 K))

/-- A Weierstrass equation for `E` that is minimal at the finite place `v` of `K`: its coefficients
lie in the valuation ring `𝓞_{K,v} = {x ∈ K | v(x) ≥ 0}` of `v`, and the `v`-adic valuation of
its discriminant is minimal among all such Weierstrass equations for `E`. -/
noncomputable abbrev minimalModelAt : WeierstrassCurve K :=
  E.minimal (v.valuation K).integer

/-- The reduction `Ẽ` modulo `v` of a Weierstrass equation for `E` that is minimal at `v`.
This is a (possibly singular) Weierstrass curve over the residue field `𝔽_v` of `v`. -/
noncomputable abbrev reductionAt :
    WeierstrassCurve (IsLocalRing.ResidueField (v.valuation K).integer) :=
  (minimalModelAt E v).reduction (v.valuation K).integer

/-- The cardinality `q_v = N(v)` of the residue field `𝔽_v` of the finite place `v`. -/
noncomputable def residueCard : ℕ :=
  Nat.card (IsLocalRing.ResidueField (v.valuation K).integer)

/-- The number `a_v = q_v + 1 - #Ẽ(𝔽_v)`, where `#Ẽ(𝔽_v)` counts all the `𝔽_v`-points of the
reduced curve `Ẽ`: the affine solutions of the reduced Weierstrass equation together with the
point at infinity, including the singular point if there is one.

For a place of good reduction this is the trace of Frobenius. For a place of bad reduction it
equals `1`, `-1` or `0` according as the reduction is split multiplicative, non-split
multiplicative or additive. -/
noncomputable def av : ℤ :=
  residueCard v - Nat.card {P : IsLocalRing.ResidueField (v.valuation K).integer ×
    IsLocalRing.ResidueField (v.valuation K).integer // (reductionAt E v).toAffine.Equation P.1 P.2}

open scoped Classical in
/-- The local Euler factor `L_v(E, s)` of the Hasse–Weil `L`-function of `E` at the finite place
`v`: it is `(1 - a_v q_v^{-s} + q_v^{1 - 2s})⁻¹` if `E` has good reduction at `v`, and
`(1 - a_v q_v^{-s})⁻¹` if `E` has bad reduction at `v`. -/
noncomputable def eulerFactor (s : ℂ) : ℂ :=
  if IsGoodReduction (v.valuation K).integer (minimalModelAt E v) then
    (1 - av E v * (residueCard v : ℂ) ^ (-s) + (residueCard v : ℂ) ^ (1 - 2 * s))⁻¹
  else
    (1 - av E v * (residueCard v : ℂ) ^ (-s))⁻¹

/-- `L : ℂ → ℂ` is the Hasse–Weil `L`-function of `E`: it is an entire function which agrees with
the Euler product `L(E, s) = ∏_v L_v(E, s)` over the finite places `v` of `K` on the half plane
`Re s > 3/2`, where the product converges.

By the identity theorem such a function is unique if it exists. Its existence is Hasse's
conjecture; over `ℚ` it follows from the modularity theorem. -/
def IsHasseWeilLFunction (L : ℂ → ℂ) : Prop :=
  Differentiable ℂ L ∧
    ∀ s : ℂ, 3 / 2 < s.re → L s = ∏' v : HeightOneSpectrum (𝓞 K), eulerFactor E v s

/-- Hasse's conjecture for elliptic curves over `ℚ`, a consequence of the modularity theorem:
the Hasse–Weil `L`-function of an elliptic curve over `ℚ` extends to an entire function. -/
theorem exists_isHasseWeilLFunction (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ L, IsHasseWeilLFunction E L := by
  sorry

end BirchAndSwinnertonDyerConjecture

theorem BirchAndSwinnertonDyerConjecture.exists_isHasseWeilLFunction.disproof : ¬ (type_of% @BirchAndSwinnertonDyerConjecture.exists_isHasseWeilLFunction) := sorry
