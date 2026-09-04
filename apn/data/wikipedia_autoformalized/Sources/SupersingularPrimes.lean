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
# Supersingular primes

Let $E$ be an elliptic curve over $\mathbb{Q}$. A prime $p$ is *supersingular* for $E$ if $E$ has
good reduction at $p$ and the reduction $\tilde{E}$ of $E$ modulo $p$ is a supersingular elliptic
curve over $\mathbb{F}_p$; equivalently, the trace of Frobenius
$a_p(E) = p + 1 - \#\tilde{E}(\mathbb{F}_p)$ is divisible by $p$ (for $p > 3$ this means
$a_p(E) = 0$, by the Hasse bound).

Lang and Trotter (1976) conjectured that, for an elliptic curve $E/\mathbb{Q}$ without complex
multiplication, the number $\pi_{E,0}(X)$ of supersingular primes $p \le X$ satisfies
$\pi_{E,0}(X) \sim C_E \sqrt{X} / \log X$ for an explicit constant $C_E > 0$. This is the entry
"Lang and Trotter's conjecture on supersingular primes that the number of supersingular primes less
than a constant $X$ is within a constant multiple of $\sqrt{X}/\ln X$" of Wikipedia's list of
unsolved problems in mathematics.

The hypothesis that $E$ has no complex multiplication is essential: for a CM curve, Deuring's
theorem shows that the supersingular primes have density $1/2$ among all primes.

*References:*
- [Wikipedia, *Supersingular prime (algebraic number theory)*](https://en.wikipedia.org/wiki/Supersingular_prime_%28algebraic_number_theory%29)
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- S. Lang and H. Trotter, *Frobenius distributions in GL₂-extensions*, Lecture Notes in
  Mathematics 504, Springer-Verlag, 1976.
- [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]
-/

namespace SupersingularPrimes

open WeierstrassCurve Filter
open scoped Asymptotics

/-- A Weierstrass curve over a finite ring has finitely many nonsingular points. -/
@[category API, AMS 11 14]
instance {R : Type*} [CommRing R] [Finite R] (W : Affine R) : Finite W.Point := by
  let f : W.Point → Option (R × R) := fun P =>
    match P with
    | .zero => none
    | .some (x := x) (y := y) _ => some (x, y)
  refine Finite.of_injective f ?_
  intro P Q h
  cases P <;> cases Q <;> simp_all [f]

section Reduction

variable (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]

/-- The reduction of `E` modulo `p`: the reduction of a minimal Weierstrass model of
`E ⊗ ℚ_p` over `ℤ_p`, which is a Weierstrass curve over the residue field `ℤ_p / pℤ_p ≅ 𝔽_p`.
It is an elliptic curve exactly when `E` has good reduction at `p`. -/
noncomputable def reductionAt : WeierstrassCurve (IsLocalRing.ResidueField ℤ_[p]) :=
  ((E.baseChange ℚ_[p]).minimal ℤ_[p]).reduction ℤ_[p]

/-- `E` has good reduction at the prime `p`: the discriminant of a minimal Weierstrass model of
`E ⊗ ℚ_p` over `ℤ_p` is a `p`-adic unit. -/
def HasGoodReductionAt : Prop :=
  IsGoodReduction ℤ_[p] ((E.baseChange ℚ_[p]).minimal ℤ_[p])

/-- The trace of Frobenius `a_p(E) = p + 1 - #Ẽ(𝔽_p)` of `E` at `p`, where `Ẽ` is the reduction
of `E` modulo `p` and `#Ẽ(𝔽_p)` counts the nonsingular affine points together with the point at
infinity. -/
noncomputable def frobeniusTrace : ℤ :=
  p + 1 - Nat.card (reductionAt E p).toAffine.Point

end Reduction

/-- A prime `p` is a *supersingular prime* for `E` if `E` has good reduction at `p` and the
reduction `Ẽ` of `E` modulo `p` is a supersingular elliptic curve over `𝔽_p`. We use the
classical characterisation of supersingularity over `𝔽_p` ([silverman2009], Exercise 5.10):
`Ẽ` is supersingular if and only if `p ∣ a_p(E)`. For `p > 3` this is equivalent to
`a_p(E) = 0`, i.e. `#Ẽ(𝔽_p) = p + 1`, by the Hasse bound `|a_p(E)| ≤ 2√p`. -/
def IsSupersingularPrime (E : WeierstrassCurve ℚ) (p : ℕ) : Prop :=
  ∃ hp : p.Prime,
    haveI := Fact.mk hp
    HasGoodReductionAt E p ∧ (p : ℤ) ∣ frobeniusTrace E p

/-- `π_{E,0}(X)`, the number of supersingular primes `p ≤ X` for `E`. -/
noncomputable def supersingularPrimeCount (E : WeierstrassCurve ℚ) (X : ℝ) : ℕ :=
  {p : ℕ | (p : ℝ) ≤ X ∧ IsSupersingularPrime E p}.ncard

/-- The thirteen `j`-invariants of elliptic curves over `ℚ` with complex multiplication. They
correspond to the thirteen imaginary quadratic orders of class number one, of discriminants
`-3, -4, -7, -8, -11, -12, -16, -19, -27, -28, -43, -67, -163` respectively. -/
def cmJInvariants : Finset ℚ :=
  {0, 12 ^ 3, -15 ^ 3, 20 ^ 3, -32 ^ 3, 2 * 30 ^ 3, 66 ^ 3, -96 ^ 3, -3 * 160 ^ 3, 255 ^ 3,
    -960 ^ 3, -5280 ^ 3, -640320 ^ 3}

/-- An elliptic curve `E` over `ℚ` has *complex multiplication* if its endomorphism ring over
`ℚ̄` is strictly larger than `ℤ` (and hence an order in an imaginary quadratic field). Mathlib
does not have the endomorphism ring of an elliptic curve, so we use the classical
characterisation: an elliptic curve over `ℚ` has complex multiplication if and only if its
`j`-invariant is one of the thirteen values in `cmJInvariants`. -/
def HasComplexMultiplication (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  E.j ∈ cmJInvariants

/-- There are exactly thirteen `j`-invariants of CM elliptic curves over `ℚ`. -/
@[category test, AMS 11 14]
theorem card_cmJInvariants : cmJInvariants.card = 13 := by
  rw [cmJInvariants]
  repeat rw [Finset.card_insert_of_notMem
    (by simp only [Finset.mem_insert, Finset.mem_singleton]; norm_num)]
  rfl

/-- The elliptic curve `y² = x³ + x`, which has complex multiplication by `ℤ[i]`. -/
def cmCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 1
  a₆ := 0

@[category test, AMS 11 14]
instance : cmCurve.IsElliptic where
  isUnit := by rw [cmCurve, Δ, b₂, b₄, b₆, b₈]; norm_num

/-- The curve `y² = x³ + x` has `j`-invariant `1728` and so has complex multiplication. -/
@[category test, AMS 11 14]
theorem hasComplexMultiplication_cmCurve : HasComplexMultiplication cmCurve := by
  have h : cmCurve.j = 1728 := by
    rw [j, Units.inv_mul_eq_iff_eq_mul, coe_Δ', cmCurve, Δ, c₄, b₂, b₄, b₆, b₈]; norm_num
  simp only [HasComplexMultiplication, h, cmJInvariants, Finset.mem_insert, Finset.mem_singleton]
  norm_num

/-- The elliptic curve `y² + y = x³ - x² - 10x - 20`, the modular curve `X₀(11)`. -/
def X₀11 : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -1
  a₃ := 1
  a₄ := -10
  a₆ := -20

@[category test, AMS 11 14]
instance : X₀11.IsElliptic where
  isUnit := by rw [X₀11, Δ, b₂, b₄, b₆, b₈]; norm_num

/-- The modular curve `X₀(11)` has `j`-invariant `-2¹² · 31³ / 11⁵` and so does not have
complex multiplication. -/
@[category test, AMS 11 14]
theorem not_hasComplexMultiplication_X₀11 : ¬ HasComplexMultiplication X₀11 := by
  have h : X₀11.j = -2 ^ 12 * 31 ^ 3 / 11 ^ 5 := by
    rw [j, Units.inv_mul_eq_iff_eq_mul, coe_Δ', X₀11, Δ, c₄, b₂, b₄, b₆, b₈]; norm_num
  simp only [HasComplexMultiplication, h, cmJInvariants, Finset.mem_insert, Finset.mem_singleton]
  norm_num

/-- **Lang–Trotter conjecture** (Lang and Trotter, 1976). Let `E` be an elliptic curve over `ℚ`
without complex multiplication. Then there is a constant `C_E > 0` such that the number
`π_{E,0}(X)` of supersingular primes `p ≤ X` for `E` satisfies
$$\pi_{E,0}(X) \sim C_E \frac{\sqrt{X}}{\log X} \quad \text{as } X \to \infty.$$
Lang and Trotter give an explicit conjectural value of $C_E$; here we only assert its
existence. -/
@[category research open, AMS 11 14]
theorem supersingular_primes (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ¬ HasComplexMultiplication E) :
    ∃ C : ℝ, 0 < C ∧
      (fun X : ℝ => (supersingularPrimeCount E X : ℝ)) ~[atTop]
        (fun X : ℝ => C * √X / Real.log X) := by
  sorry

/-- A weaker form of the Lang–Trotter conjecture, as worded in Wikipedia's list of unsolved
problems: for an elliptic curve `E` over `ℚ` without complex multiplication, the number
`π_{E,0}(X)` of supersingular primes `p ≤ X` for `E` is within a constant multiple of
`√X / log X`, i.e. there are constants `c₁, c₂ > 0` with
$$c_1 \frac{\sqrt{X}}{\log X} \le \pi_{E,0}(X) \le c_2 \frac{\sqrt{X}}{\log X}$$
for all sufficiently large `X`. -/
@[category research open, AMS 11 14]
theorem supersingular_primes.variants.weaker (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ¬ HasComplexMultiplication E) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ X : ℝ in atTop,
      c₁ * √X / Real.log X ≤ supersingularPrimeCount E X ∧
        (supersingularPrimeCount E X : ℝ) ≤ c₂ * √X / Real.log X := by
  sorry

end SupersingularPrimes
