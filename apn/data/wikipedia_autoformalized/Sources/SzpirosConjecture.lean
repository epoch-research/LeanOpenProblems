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
# Szpiro's conjecture

Szpiro's conjecture relates the minimal discriminant of an elliptic curve over $\mathbb{Q}$ to
its conductor: for any $\varepsilon > 0$ there is a constant $C(\varepsilon)$ such that every
elliptic curve $E$ over $\mathbb{Q}$ with minimal discriminant $\Delta$ and conductor $f$
satisfies $|\Delta| \leq C(\varepsilon) \cdot f^{6 + \varepsilon}$.

Mathlib has neither the global minimal discriminant nor the conductor of an elliptic curve over
$\mathbb{Q}$, so both are defined in this file.

* A *global minimal model* of `E` is a Weierstrass equation with integer coefficients that is
  isomorphic to `E` over $\mathbb{Q}$ and is minimal at every prime, i.e. its discriminant divides
  the discriminant of every integral model of `E`. Such a model exists because $\mathbb{Q}$ has
  class number one, and its discriminant is the minimal discriminant of `E`.
* The conductor is $f = \prod_p p^{f_p}$ where $f_p = \varepsilon_p + \delta_p$. The tame part
  $\varepsilon_p$ is $0$, $1$ or $2$ according as `E` has good, multiplicative or additive
  reduction at $p$. The wild part $\delta_p$ is the Swan conductor of the Galois module $E[\ell]$
  for a prime $\ell \neq p$, computed with the higher ramification groups of a prime above $p$ in
  a Galois number field containing all $\ell$-torsion points of `E`. See Silverman,
  *Advanced Topics in the Arithmetic of Elliptic Curves*, Chapter IV, §10.

*References:*
- [Wikipedia, Szpiro's conjecture](https://en.wikipedia.org/wiki/Szpiro%27s_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer, 2009,
  Chapters VII and VIII
- J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, Springer,
  1994, Chapter IV, §10
-/

namespace SzpirosConjecture

open WeierstrassCurve
open scoped WeierstrassCurve.Affine NumberField

/-- A Weierstrass equation `W` with integer coefficients is an *integral model* of the curve `E`
over $\mathbb{Q}$ if `E` is isomorphic over $\mathbb{Q}$ to `W`, i.e. `E` is carried to `W` by a
change of variables over $\mathbb{Q}$. -/
def IsIntegralModel (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ) : Prop :=
  ∃ C : VariableChange ℚ, C • E = W.baseChange ℚ

/-- A *global minimal model* of `E` is an integral model of `E` whose discriminant divides the
discriminant of every integral model of `E`. Equivalently, it is an integral Weierstrass equation
for `E` that is minimal at every prime `p`, i.e. $v_p(\Delta)$ is as small as possible.
Every elliptic curve over $\mathbb{Q}$ has a global minimal model, since $\mathbb{Q}$ has class
number one, and the discriminant of a global minimal model is the *minimal discriminant* of `E`.
-/
def IsGlobalMinimalModel (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ) : Prop :=
  IsIntegralModel E W ∧ ∀ W' : WeierstrassCurve ℤ, IsIntegralModel E W' → W.Δ ∣ W'.Δ

/-- The *tame part* $\varepsilon_p$ of the conductor exponent at the prime `p` of a Weierstrass
equation `W` over `ℤ` that is minimal at `p`. It is `0` if the reduction of `W` modulo `p` is
nonsingular (good reduction), `1` if it has a node (multiplicative reduction, i.e. $p \mid \Delta$
and $p \nmid c_4$), and `2` if it has a cusp (additive reduction, i.e. $p \mid \Delta$ and
$p \mid c_4$). -/
def tameConductorExponent (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  if (p : ℤ) ∣ W.Δ then (if (p : ℤ) ∣ W.c₄ then 2 else 1) else 0

variable {L : Type*} [Field L] [NumberField L]

/-- The `i`-th ramification group (in the lower numbering) of a prime `𝔓` of the number field `L`
in the Galois group $\mathrm{Gal}(L/\mathbb{Q})$: the automorphisms $\sigma$ with
$\sigma(x) \equiv x \pmod{\mathfrak{P}^{i+1}}$ for all $x \in \mathcal{O}_L$. For `i = 0` this is
the inertia group of `𝔓`. -/
def ramificationGroup (𝔓 : Ideal (𝓞 L)) (i : ℕ) : Subgroup (L ≃ₐ[ℚ] L) :=
  (𝔓 ^ (i + 1)).toAddSubgroup.inertia (L ≃ₐ[ℚ] L)

open scoped Classical in
/-- The `ℓ`-torsion points of `E` with coordinates in `L` that are fixed by every element of the
subgroup `H` of $\mathrm{Gal}(L/\mathbb{Q})$, i.e. the fixed points $E[\ell]^H$ when `L` contains
all `ℓ`-torsion points of `E`. -/
def fixedTorsion (E : WeierstrassCurve ℚ) (H : Subgroup (L ≃ₐ[ℚ] L)) (ℓ : ℕ) : Set E⟮L⟯ :=
  {P | ℓ • P = 0 ∧ ∀ σ ∈ H, Affine.Point.map σ.toAlgHom P = P}

/-- The *Swan conductor* (wild part of the conductor exponent) of `E` at the prime `𝔓` of `L`,
computed from the `ℓ`-torsion of `E`, where `L` is a Galois number field containing all
`ℓ`-torsion points of `E` and `ℓ` is a prime different from the residue characteristic of `𝔓`:
$$\delta = \sum_{i \geq 1} \frac{|G_i|}{|G_0|} \dim_{\mathbb{F}_\ell}
  \left(E[\ell] / E[\ell]^{G_i}\right),$$
where $G_i$ is the `i`-th ramification group of `𝔓`. Here $\dim_{\mathbb{F}_\ell} E[\ell] = 2$
and $\dim_{\mathbb{F}_\ell} E[\ell]^{G_i} = \log_\ell |E[\ell]^{G_i}|$. The sum is finite since
$G_i$ is trivial for `i` large. -/
noncomputable def swanConductor (E : WeierstrassCurve ℚ) (𝔓 : Ideal (𝓞 L)) (ℓ : ℕ) : ℚ :=
  ∑ᶠ i : ℕ, (Nat.card (ramificationGroup 𝔓 (i + 1)) : ℚ) / Nat.card (ramificationGroup 𝔓 0) *
    (2 - (Nat.log ℓ (Nat.card (fixedTorsion E (ramificationGroup 𝔓 (i + 1)) ℓ)) : ℚ))

open scoped Classical in
/-- `n` is the exponent $f_p$ of the prime `p` in the conductor of `E`, where `W` is a global
minimal model of `E`: $f_p = \varepsilon_p + \delta_p$ is the sum of the tame part, read off from
the reduction of `W` modulo `p`, and the Swan conductor. The latter is computed from the
`ℓ`-torsion of `E` for any prime `ℓ ≠ p`, in any Galois number field `L` containing all
`ℓ`-torsion points of `E`, at any prime `𝔓` of `L` above `p`; the result does not depend on these
choices. -/
def IsConductorExponent (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ) (p n : ℕ) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
    ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
      Nat.card {P : E⟮L⟯ | ℓ • P = 0} = ℓ ^ 2 →
        ∀ 𝔓 : Ideal (𝓞 L), 𝔓.IsMaximal → (p : 𝓞 L) ∈ 𝔓 →
          (n : ℚ) = tameConductorExponent W p + swanConductor E 𝔓 ℓ

/-- `N` is the *conductor* of the elliptic curve `E` over $\mathbb{Q}$: `N` is the positive
integer $\prod_p p^{f_p}$ whose exponent at every prime `p` is the conductor exponent $f_p$ of
`E` at `p`, computed with any global minimal model of `E`. -/
def IsConductor (E : WeierstrassCurve ℚ) (N : ℕ) : Prop :=
  0 < N ∧ ∀ W : WeierstrassCurve ℤ, IsGlobalMinimalModel E W →
    ∀ p : ℕ, p.Prime → IsConductorExponent E W p (padicValNat p N)

/-- An integral Weierstrass equation is an integral model of its base change to $\mathbb{Q}$. -/
@[category test, AMS 11 14]
theorem isIntegralModel_baseChange (W : WeierstrassCurve ℤ) :
    IsIntegralModel (W.baseChange ℚ) W :=
  ⟨1, one_smul _ _⟩

/-- The curve $y^2 = x^3 - x$ has discriminant $64$, so it has good reduction at $3$. -/
@[category test, AMS 11 14]
theorem tameConductorExponent_three : tameConductorExponent ⟨0, 0, 0, -1, 0⟩ 3 = 0 := by
  simp [tameConductorExponent, Δ, b₂, b₄, b₆, b₈]

/-- The curve $y^2 = x^3 - x$ has $\Delta = 64$ and $c_4 = 48$, so it has additive reduction
at $2$. -/
@[category test, AMS 11 14]
theorem tameConductorExponent_two : tameConductorExponent ⟨0, 0, 0, -1, 0⟩ 2 = 2 := by
  simp [tameConductorExponent, Δ, c₄, b₂, b₄, b₆, b₈]

/-- The curve $y^2 = x^3 + x^2 - x$ has $\Delta = 80$ and $c_4 = 64$, so it has multiplicative
reduction at $5$. -/
@[category test, AMS 11 14]
theorem tameConductorExponent_five : tameConductorExponent ⟨0, 1, 0, -1, 0⟩ 5 = 1 := by
  simp [tameConductorExponent, Δ, c₄, b₂, b₄, b₆, b₈]

/-- The `0`-th ramification group of `𝔓` is the inertia group of `𝔓`. -/
@[category test, AMS 11]
theorem ramificationGroup_zero (𝔓 : Ideal (𝓞 L)) :
    ramificationGroup 𝔓 0 = 𝔓.toAddSubgroup.inertia (L ≃ₐ[ℚ] L) := by
  simp [ramificationGroup]

/-- **Szpiro's conjecture**: for any $\varepsilon > 0$, there is some constant $C(\varepsilon)$
such that, for any elliptic curve $E$ defined over $\mathbb{Q}$ with minimal discriminant
$\Delta$ and conductor $f$, we have $|\Delta| \leq C(\varepsilon) \cdot f^{6+\varepsilon}$.

Here $\Delta$ is the discriminant of a global minimal model `W` of `E` and $f$ is the conductor
`N` of `E`. The constant $C(\varepsilon)$ is a positive real number depending only on
$\varepsilon$. -/
@[category research open, AMS 11 14]
theorem szpiros_conjecture (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (W : WeierstrassCurve ℤ) (N : ℕ),
      IsGlobalMinimalModel E W → IsConductor E N → |(W.Δ : ℝ)| ≤ C * (N : ℝ) ^ (6 + ε) := by
  sorry

end SzpirosConjecture
