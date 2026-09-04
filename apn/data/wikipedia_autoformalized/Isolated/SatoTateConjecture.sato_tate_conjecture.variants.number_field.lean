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
# Sato–Tate conjecture

Let $E$ be an elliptic curve over $\mathbb{Q}$ without complex multiplication. For a prime $p$
let $N_p$ be the number of points of the reduction of $E$ modulo $p$ over $\mathbb{F}_p$, and
define $\theta_p \in [0, \pi]$ by $p + 1 - N_p = 2\sqrt{p}\cos\theta_p$. The **Sato–Tate
conjecture** states that the angles $\theta_p$ are equidistributed with respect to the measure
$\frac{2}{\pi}\sin^2\theta\,d\theta$ on $[0, \pi]$: for all $0 \le \alpha < \beta \le \pi$,
$$\lim_{N \to \infty} \frac{\#\{p \le N : \alpha \le \theta_p \le \beta\}}{\#\{p \le N\}}
  = \frac{2}{\pi}\int_\alpha^\beta \sin^2\theta\,d\theta.$$

The conjecture and its generalisation to totally real fields were proved by Clozel, Harris,
Shepherd-Barron and Taylor (2008, under a mild hypothesis) and by Barnet-Lamb, Geraghty, Harris
and Taylor (2011). The latter also proved the analogue for non-CM holomorphic cuspidal newforms of
weight at least two. The analogue for elliptic curves over an arbitrary number field is open.

## Formalisation notes

* Mathlib has no notion of the endomorphism ring of an elliptic curve. Complex multiplication is
  therefore defined analytically: an elliptic curve `E` over a field `K` has complex
  multiplication if, for some (equivalently, every) embedding `σ : K → ℂ`, `σ(j(E))` is a
  *singular modulus*, i.e. `σ(j(E)) = j(τ)` for an imaginary quadratic point `τ` of the upper
  half-plane, where `j = 1728 E₄³ / (E₄³ - E₆²)` is the modular `j`-function.
* The reduction of `E` at a finite place `v` is the reduction of a `v`-minimal model of `E`
  (`WeierstrassCurve.minimal` and `WeierstrassCurve.reduction` from Mathlib). Its number of
  points is the number of solutions of the Weierstrass equation over the residue field plus one
  (the point at infinity).
* Over `ℚ` the statement counts all primes, as in the source. At the finitely many primes of
  bad reduction the angle `θ_p` is still defined (there `a_p ∈ {0, ±1}`) and these primes do
  not affect the limit. Over a number field the statement counts places of good reduction, ordered
  by norm.
* A normalised Hecke eigenform is defined through the multiplicative relations satisfied by its
  Fourier coefficients (Diamond–Shurman, Proposition 5.8.5), since Mathlib has no Hecke
  operators. A cusp form has complex multiplication if it is fixed by a twist by a non-trivial
  Dirichlet character (Ribet).

*References:*
- [Wikipedia, *Sato–Tate conjecture*](https://en.wikipedia.org/wiki/Sato%E2%80%93Tate_conjecture)
- Wikipedia, *List of unsolved problems in mathematics*,
  https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics
- L. Clozel, M. Harris, R. Taylor, *Automorphy for some l-adic lifts of automorphic mod l
  Galois representations*, Publ. Math. IHÉS 108 (2008), https://doi.org/10.1007/s10240-008-0016-1
- M. Harris, N. Shepherd-Barron, R. Taylor, *A family of Calabi–Yau varieties and potential
  automorphy*, Ann. of Math. 171 (2010), https://doi.org/10.4007/annals.2010.171.779
- T. Barnet-Lamb, D. Geraghty, M. Harris, R. Taylor, *A family of Calabi–Yau varieties and
  potential automorphy II*, Publ. RIMS 47 (2011), https://doi.org/10.2977/PRIMS/31
- K. Ribet, *Galois representations attached to eigenforms with Nebentypus*, LNM 601 (1977)
- [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005]
- [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]
-/

namespace SatoTateConjecture

open Filter IsDedekindDomain NumberField Real SatoTateConjecture
open scoped Topology UpperHalfPlane

/- ### Complex multiplication -/

open ModularForm in
/-- The modular `j`-function `j(τ) = 1728 E₄(τ)³ / (E₄(τ)³ - E₆(τ)²)` on the upper half-plane,
where `E₄` and `E₆` are the normalised Eisenstein series of level one (constant term `1`). -/
noncomputable def jFunction (τ : ℍ) : ℂ :=
  1728 * E (k := 4) (by norm_num) τ ^ 3 /
    (E (k := 4) (by norm_num) τ ^ 3 - E (k := 6) (by norm_num) τ ^ 2)

/-- A point `τ` of the upper half-plane is a *CM point* if it is imaginary quadratic, i.e. a root
of a quadratic polynomial with integer coefficients. -/
def IsCMPoint (τ : ℍ) : Prop :=
  ∃ a b c : ℤ, a ≠ 0 ∧ a * (τ : ℂ) ^ 2 + b * (τ : ℂ) + c = 0

/-- An elliptic curve `E` over a field `K` has *complex multiplication* if its `j`-invariant is a
singular modulus: for some embedding `σ : K → ℂ` there is a CM point `τ` with
`σ(j(E)) = j(τ)`. Equivalently, `E` is isomorphic over `ℂ` to `ℂ / (ℤ + τℤ)` with `τ` imaginary
quadratic, i.e. the endomorphism ring of `E` over an algebraic closure of `K` is larger than
`ℤ`. Since the singular moduli are permuted by `Gal(ℚ̄ / ℚ)`, the choice of `σ` is irrelevant. -/
def WeierstrassCurve.HasComplexMultiplication {K : Type*} [Field K] (E : WeierstrassCurve K)
    [E.IsElliptic] : Prop :=
  ∃ (σ : K →+* ℂ) (τ : ℍ), IsCMPoint τ ∧ σ E.j = jFunction τ

/- ### Point counts, Frobenius angles and the Sato–Tate measure -/

/-- The number of points of a Weierstrass curve `W` over a field `F`: the number of solutions of
the (affine) Weierstrass equation plus one for the point at infinity. -/
noncomputable def numPoints {F : Type*} [Field F] (W : WeierstrassCurve F) : ℕ :=
  Nat.card {P : F × F // W.toAffine.Equation P.1 P.2} + 1

/-- The number of points of the reduction of a Weierstrass curve `E` over the fraction field `K`
of a discrete valuation ring `R`: a minimal model of `E` over `R` is reduced modulo the maximal
ideal of `R`, and its points over the residue field are counted. -/
noncomputable def numPointsReduction (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (E : WeierstrassCurve K) : ℕ :=
  numPoints ((E.minimal R).reduction R)

/-- The angle `θ ∈ [0, π]` attached to an integer `a` and a natural number `q` by
`a = 2 √q cos θ`. For `a` a trace of Frobenius over `𝔽_q` the Hasse bound gives `|a| ≤ 2 √q`,
so `θ` is well defined. -/
noncomputable def frobeniusAngle (a : ℤ) (q : ℕ) : ℝ :=
  arccos (a / (2 * √(q : ℝ)))

/-- The Sato–Tate measure `(2 / π) sin² θ dθ` of the interval `[α, β]`. -/
noncomputable def satoTateMeasure (α β : ℝ) : ℝ :=
  2 / π * ∫ θ in α..β, sin θ ^ 2

/- ### Elliptic curves over `ℚ` -/

/-- The trace of Frobenius `a_p(E) = p + 1 - N_p` of a Weierstrass curve `E` over `ℚ` at a prime
`p`, where `N_p` is the number of points over `𝔽_p` of the reduction modulo `p` of a minimal model
of `E` at `p`. -/
noncomputable def WeierstrassCurve.apRat (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] : ℤ :=
  p + 1 - numPointsReduction ℤ_[p] (E.baseChange ℚ_[p])

/-- The Frobenius angle `θ_p ∈ [0, π]` of a Weierstrass curve `E` over `ℚ` at a prime `p`,
defined by `p + 1 - N_p = 2 √p cos θ_p`. -/
noncomputable def WeierstrassCurve.thetaRat (E : WeierstrassCurve ℚ) (p : Nat.Primes) : ℝ :=
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  frobeniusAngle (E.apRat p) p

/- ### Elliptic curves over number fields -/

section NumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- A Weierstrass curve `E` over a number field `K` has good reduction at a finite place `v` if
a `v`-minimal model of `E` has discriminant of valuation zero at `v`. -/
def WeierstrassCurve.HasGoodReduction (E : WeierstrassCurve K) (v : HeightOneSpectrum (𝓞 K)) :
    Prop :=
  WeierstrassCurve.IsGoodReduction (v.valuation K).integer (E.minimal (v.valuation K).integer)

/-- The trace of Frobenius `a_v(E) = q_v + 1 - N_v` of a Weierstrass curve `E` over a number field
`K` at a finite place `v`, where `q_v` is the norm of `v` and `N_v` is the number of points over
the residue field of the reduction at `v` of a `v`-minimal model of `E`. -/
noncomputable def WeierstrassCurve.av (E : WeierstrassCurve K) (v : HeightOneSpectrum (𝓞 K)) :
    ℤ :=
  Ideal.absNorm v.asIdeal + 1 - numPointsReduction (v.valuation K).integer E

/-- The Frobenius angle `θ_v ∈ [0, π]` of a Weierstrass curve `E` over a number field `K` at a
finite place `v`, defined by `a_v(E) = 2 √q_v cos θ_v`. -/
noncomputable def WeierstrassCurve.theta (E : WeierstrassCurve K)
    (v : HeightOneSpectrum (𝓞 K)) : ℝ :=
  frobeniusAngle (E.av v) (Ideal.absNorm v.asIdeal)

/-- The finite places `v` of `K` of norm at most `X` at which `E` has good reduction. -/
def WeierstrassCurve.goodPlacesLE (E : WeierstrassCurve K) (X : ℕ) :
    Set (HeightOneSpectrum (𝓞 K)) :=
  {v | Ideal.absNorm v.asIdeal ≤ X ∧ E.HasGoodReduction v}

/--
**Sato–Tate conjecture for number fields.** Let $E$ be an elliptic curve without complex
multiplication over a number field $K$. For a finite place $v$ of good reduction with residue
field of size $q_v$, define $\theta_v \in [0, \pi]$ by
$q_v + 1 - \#E(\mathbb{F}_v) = 2\sqrt{q_v}\cos\theta_v$. Then, ordering the places by norm, the
angles $\theta_v$ are equidistributed with respect to $\frac{2}{\pi}\sin^2\theta\,d\theta$: for
all $0 \le \alpha < \beta \le \pi$,
$$\lim_{X \to \infty}
  \frac{\#\{v : N(v) \le X,\ \alpha \le \theta_v \le \beta\}}{\#\{v : N(v) \le X\}}
  = \frac{2}{\pi}\int_\alpha^\beta \sin^2\theta\,d\theta,$$
where $v$ ranges over the finite places of good reduction.

This is known for totally real fields and for CM fields, but open for a general number field.
-/
theorem sato_tate_conjecture.variants.number_field (E : WeierstrassCurve K) [E.IsElliptic]
    (hE : ¬ E.HasComplexMultiplication) {α β : ℝ} (hα : 0 ≤ α) (hαβ : α < β) (hβ : β ≤ π) :
    Tendsto (fun X : ℕ ↦
        ({v ∈ E.goodPlacesLE X | E.theta v ∈ Set.Icc α β}.ncard : ℝ) / (E.goodPlacesLE X).ncard)
      atTop (𝓝 (satoTateMeasure α β)) := by
  sorry

end NumberFields

/- ### Modular forms -/

section ModularForms

open CongruenceSubgroup ModularFormClass

variable {N : ℕ} {k : ℤ}

/-- The `n`-th Fourier coefficient `a_n(f)` of a cusp form `f` for `Γ₀(N)` at the cusp at
infinity, i.e. `f(τ) = ∑ a_n(f) e^{2πinτ}`. -/
noncomputable def modularFormAn (n : ℕ) (f : CuspForm (Gamma0 N) k) : ℂ :=
  (qExpansion 1 f).coeff n

local notation:73 "a_[" n:0 "]" f:72 => modularFormAn n f

/-- A cusp form `f` for `Γ₀(N)` is a *normalised Hecke eigenform* if `a_1(f) = 1` and its Fourier
coefficients satisfy the multiplicative relations of the Hecke eigenvalues (Diamond–Shurman,
Proposition 5.8.5, with trivial character): `a_{mn} = a_m a_n` for coprime `m, n`,
`a_{p^r} = a_p a_{p^{r-1}} - p^{k-1} a_{p^{r-2}}` for primes `p ∤ N` and
`a_{p^r} = a_p^r` for primes `p ∣ N`. -/
def IsNormalisedEigenform (f : CuspForm (Gamma0 N) k) : Prop :=
  a_[1] f = 1 ∧
  (∀ m n : ℕ, m.Coprime n → a_[m * n] f = a_[m] f * a_[n] f) ∧
  (∀ p r : ℕ, p.Prime → 2 ≤ r → ¬ p ∣ N →
    a_[p ^ r] f = a_[p] f * a_[p ^ (r - 1)] f - (p : ℂ) ^ (k - 1) * a_[p ^ (r - 2)] f) ∧
  ∀ p r : ℕ, p.Prime → 2 ≤ r → p ∣ N → a_[p ^ r] f = (a_[p] f) ^ r

/-- A cusp form `f` for `Γ₀(N)` has *complex multiplication* (Ribet) if it is fixed by the twist
by some non-trivial Dirichlet character `χ` modulo `M`, i.e. `χ(p) a_p(f) = a_p(f)` for all primes
`p ∤ N M`. Equivalently, `f` arises from a Hecke character of an imaginary quadratic field. -/
def CuspForm.HasComplexMultiplication (f : CuspForm (Gamma0 N) k) : Prop :=
  ∃ (M : ℕ+) (χ : DirichletCharacter ℂ M), χ ≠ 1 ∧
    ∀ p : ℕ, p.Prime → ¬ p ∣ N * M → χ p * a_[p] f = a_[p] f

/-- The angle `θ_p ∈ [0, π]` attached to a cusp form `f` of weight `k` for `Γ₀(N)` at a prime
`p`, defined by `a_p(f) = 2 p^{(k-1)/2} cos θ_p`. For a Hecke eigenform with trivial character
`a_p(f)` is real and, by Deligne's bound, `|a_p(f)| ≤ 2 p^{(k-1)/2}` for `p ∤ N`. -/
noncomputable def CuspForm.theta (f : CuspForm (Gamma0 N) k) (p : ℕ) : ℝ :=
  arccos ((a_[p] f).re / (2 * (p : ℝ) ^ (((k : ℝ) - 1) / 2)))

end ModularForms

end SatoTateConjecture

theorem SatoTateConjecture.sato_tate_conjecture.variants.number_field.disproof : ¬ (type_of% @SatoTateConjecture.sato_tate_conjecture.variants.number_field) := sorry
