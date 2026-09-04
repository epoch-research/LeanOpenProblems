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
# Kazhdan–Lusztig conjectures

The Kazhdan–Lusztig conjectures relate the values at $q = 1$ of the Kazhdan–Lusztig polynomials
$P_{y,w}$ of a finite Weyl group $W$ to the representation theory of the corresponding complex
semisimple Lie algebra $\mathfrak{g}$.

Let $\mathfrak{h} \subseteq \mathfrak{g}$ be a Cartan subalgebra, fix a base of the root system
(equivalently, a system of positive roots), and let $\rho$ be the half-sum of the positive roots.
For $w \in W$ let $M_w$ be the Verma module of highest weight $-w(\rho) - \rho$ and let $L_w$ be
its unique simple quotient. Writing $\operatorname{ch}$ for the formal character, the conjectures
state that for all $w \in W$
$$\operatorname{ch}(L_w) =
  \sum_{y \le w} (-1)^{\ell(w) - \ell(y)} P_{y,w}(1) \operatorname{ch}(M_y)$$
and
$$\operatorname{ch}(M_w) = \sum_{y \le w} P_{w_0 w, w_0 y}(1) \operatorname{ch}(L_y),$$
where $\le$ is the Bruhat order, $\ell$ is the Coxeter length and $w_0$ is the longest element
of $W$. Both were proved in 1981 by Beilinson–Bernstein and by Brylinski–Kashiwara.

Mathlib does not contain Kazhdan–Lusztig polynomials, the Bruhat order or Verma modules. This
file defines the Bruhat order and characterises the $R$-polynomials and the Kazhdan–Lusztig
polynomials by the standard axioms (Björner–Brenti, Theorems 5.1.1 and 5.1.4), which determine
them uniquely; the conjectures are then stated for any family of polynomials satisfying these
axioms. Verma modules are constructed as quotients of the universal enveloping algebra.

A complex semisimple Lie algebra is modelled as a finite-dimensional Lie algebra over $\mathbb{C}$
with non-degenerate Killing form (`LieAlgebra.IsKilling`); by Cartan's criterion this is
equivalent to semisimplicity. The Weyl group is `RootPairing.weylGroup` of the root system of
$\mathfrak{g}$. Mathlib does not yet know that it is finite, nor that it is a Coxeter group with
respect to the simple reflections, so both facts are taken as hypotheses.

*References:*
- [Wikipedia, Kazhdan–Lusztig polynomial](https://en.wikipedia.org/wiki/Kazhdan%E2%80%93Lusztig_polynomial%23Kazhdan%E2%80%93Lusztig_conjectures)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- D. Kazhdan, G. Lusztig, *Representations of Coxeter groups and Hecke algebras*,
  Invent. Math. 53 (1979), 165–184.
- A. Björner, F. Brenti, *Combinatorics of Coxeter Groups*, GTM 231, Springer, 2005, Chapter 5.
- J. E. Humphreys, *Representations of Semisimple Lie Algebras in the BGG Category $\mathcal{O}$*,
  GSM 94, AMS, 2008, Sections 1.3 and 8.4.
-/

namespace KazhdanLusztigConjectures

open Polynomial

section Coxeter

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "ℓ" => cs.length

/-- The Bruhat order on a Coxeter group: `u ≤ v` if there is a chain
`u = x₀ → x₁ → ⋯ → xₖ = v` where each step is `xⱼ → xⱼ t` for a reflection `t`
with `ℓ(xⱼ) < ℓ(xⱼ t)` (Björner–Brenti, Definition 2.1.1). -/
def BruhatLE (u v : W) : Prop :=
  Relation.ReflTransGen (fun x y => ∃ t, cs.IsReflection t ∧ y = x * t ∧ ℓ x < ℓ y) u v

local infix:50 " ≤ᴮ " => BruhatLE cs

/-- `IsRPolynomials cs R` says that `R : W → W → ℤ[X]` is the family of $R$-polynomials
$R_{u,v}(q)$ of the Coxeter system `cs`. These are the polynomials with
* $R_{u,v} = 0$ unless $u \le v$ in the Bruhat order,
* $R_{v,v} = 1$,
* for a right descent $s$ of $v$: $R_{u,v} = R_{us,vs}$ if $s$ is a right descent of $u$, and
  $R_{u,v} = (q - 1) R_{u,vs} + q R_{us,vs}$ otherwise.

These conditions determine the family uniquely (Björner–Brenti, Theorem 5.1.1). -/
structure IsRPolynomials (R : W → W → ℤ[X]) : Prop where
  eq_zero_of_not_bruhatLE (u v : W) : ¬ u ≤ᴮ v → R u v = 0
  self (v : W) : R v v = 1
  of_isRightDescent (u v : W) (i : B) : cs.IsRightDescent v i → cs.IsRightDescent u i →
    R u v = R (u * s i) (v * s i)
  of_not_isRightDescent (u v : W) (i : B) : cs.IsRightDescent v i → ¬ cs.IsRightDescent u i →
    R u v = (X - 1) * R u (v * s i) + X * R (u * s i) (v * s i)

variable [Fintype W]

open scoped Classical in
/-- `IsKazhdanLusztigPolynomials cs R P` says that `P : W → W → ℤ[X]` is the family of
Kazhdan–Lusztig polynomials $P_{u,v}(q)$ of the finite Coxeter system `cs`, given that `R` is
the family of $R$-polynomials. These are the polynomials with
* $P_{u,v} = 0$ unless $u \le v$ in the Bruhat order,
* $P_{v,v} = 1$,
* $\deg P_{u,v} \le (\ell(v) - \ell(u) - 1)/2$ for $u < v$,
* $q^{\ell(v) - \ell(u)} P_{u,v}(q^{-1}) = \sum_{u \le a \le v} R_{u,a}(q) P_{a,v}(q)$ for
  $u \le v$.

These conditions determine the family uniquely (Björner–Brenti, Theorem 5.1.4). The left hand
side of the last condition is expressed with `Polynomial.reflect n p`, which is $q^n p(q^{-1})$
whenever $\deg p \le n$. -/
structure IsKazhdanLusztigPolynomials (R P : W → W → ℤ[X]) : Prop where
  eq_zero_of_not_bruhatLE (u v : W) : ¬ u ≤ᴮ v → P u v = 0
  self (v : W) : P v v = 1
  degree_le (u v : W) : u ≤ᴮ v → u ≠ v →
    (P u v).degree ≤ ((ℓ v - ℓ u - 1) / 2 : ℕ)
  reflect_eq (u v : W) : u ≤ᴮ v →
    (P u v).reflect (ℓ v - ℓ u) =
      ∑ a ∈ Finset.univ.filter (fun a => u ≤ᴮ a ∧ a ≤ᴮ v), R u a * P a v

end Coxeter

section LieAlgebra

open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [IsKilling ℂ L] [FiniteDimensional ℂ L]
  {H : LieSubalgebra ℂ L} [H.IsCartanSubalgebra]

local notation "Φ" => IsKilling.rootSystem H
local notation "𝔚" => RootPairing.weylGroup Φ

variable (b : RootPairing.Base (LieAlgebra.IsKilling.rootSystem H))

open scoped Classical in
/-- The Weyl vector $\rho$: half the sum of the positive roots (positive with respect to the
base `b`). -/
noncomputable def weylVector : Dual ℂ H :=
  (2 : ℂ)⁻¹ • ∑ α : H.root with b.IsPos α, RootPairing.root Φ α

/-- The nilpotent subalgebra $\mathfrak{n}^+ = \bigoplus_{\alpha > 0} \mathfrak{g}_\alpha$
spanned by the root spaces of the positive roots, as a subspace of the Lie algebra. -/
noncomputable def positiveNilradical : Submodule ℂ L :=
  ⨆ α : H.root, ⨆ (_ : b.IsPos α), (rootSpace H (α : H → ℂ)).toSubmodule

local notation "𝒰" => UniversalEnvelopingAlgebra ℂ L

/-- The left ideal $I_\lambda$ of the universal enveloping algebra $U(\mathfrak{g})$ generated by
$\mathfrak{n}^+$ and by the elements $h - \lambda(h) \cdot 1$ for $h \in \mathfrak{h}$. -/
noncomputable def vermaIdeal (χ : Dual ℂ H) : Submodule 𝒰 𝒰 :=
  Submodule.span 𝒰
    (UniversalEnvelopingAlgebra.ι ℂ '' (positiveNilradical b : Set L) ∪
      Set.range fun h : H => UniversalEnvelopingAlgebra.ι ℂ (h : L) - algebraMap ℂ 𝒰 (χ h))

/-- The Verma module $M(\lambda) = U(\mathfrak{g}) / I_\lambda$ of highest weight $\lambda$.
It is isomorphic to $U(\mathfrak{g}) \otimes_{U(\mathfrak{b})} \mathbb{C}_\lambda$
(Humphreys, Section 1.3). -/
abbrev VermaModule (χ : Dual ℂ H) : Type _ :=
  𝒰 ⧸ vermaIdeal b χ

/-- The Lie algebra $\mathfrak{g}$ acts on $M(\lambda)$ through $U(\mathfrak{g})$. -/
noncomputable instance (χ : Dual ℂ H) : LieRingModule L (VermaModule b χ) :=
  letI : LieRingModule 𝒰 (VermaModule b χ) := LieRingModule.ofAssociativeModule
  LieRingModule.compLieHom (VermaModule b χ) (UniversalEnvelopingAlgebra.ι ℂ)

noncomputable instance (χ : Dual ℂ H) : LieModule ℂ L (VermaModule b χ) :=
  letI : LieRingModule 𝒰 (VermaModule b χ) := LieRingModule.ofAssociativeModule
  haveI : LieModule ℂ 𝒰 (VermaModule b χ) := LieModule.ofAssociativeModule
  LieModule.compLieHom (VermaModule b χ) (UniversalEnvelopingAlgebra.ι ℂ)

/-- The unique maximal proper submodule $N(\lambda)$ of the Verma module $M(\lambda)$, defined as
the sum of all proper submodules. -/
noncomputable def vermaMaximalSubmodule (χ : Dual ℂ H) : LieSubmodule ℂ L (VermaModule b χ) :=
  sSup {N | N ≠ ⊤}

/-- The simple highest weight module $L(\lambda) = M(\lambda) / N(\lambda)$ of highest weight
$\lambda$: the unique simple quotient of the Verma module $M(\lambda)$. -/
abbrev SimpleHighestWeightModule (χ : Dual ℂ H) : Type _ :=
  VermaModule b χ ⧸ vermaMaximalSubmodule b χ

variable (H) in
/-- The formal character of a $\mathfrak{g}$-module $X$: the function
$\mu \mapsto \dim X_\mu$ recording the dimensions of the weight spaces
$X_\mu = \{x \in X \mid h \cdot x = \mu(h) x \text{ for all } h \in \mathfrak{h}\}$,
i.e. the formal sum $\operatorname{ch}(X) = \sum_\mu \dim X_\mu \, e^\mu$. -/
noncomputable def formalCharacter (X : Type*) [AddCommGroup X] [Module ℂ X] [LieRingModule L X]
    [LieModule ℂ L X] : Dual ℂ H → ℤ :=
  fun μ => finrank ℂ (weightSpace X (μ : H → ℂ))

end LieAlgebra

section Conjectures

open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [IsKilling ℂ L] [FiniteDimensional ℂ L]
  {H : LieSubalgebra ℂ L} [H.IsCartanSubalgebra]

local notation "Φ" => IsKilling.rootSystem H
local notation "𝔚" => RootPairing.weylGroup Φ

open scoped Classical in
/--
**Second Kazhdan–Lusztig conjecture** (Kazhdan–Lusztig 1979; proved by Beilinson–Bernstein and
Brylinski–Kashiwara, 1981). It is equivalent to the first conjecture.

With notation as in the first conjecture, for every $w \in W$
$$\operatorname{ch}(M_w) = \sum_{y \le w} P_{w_0 w, w_0 y}(1) \operatorname{ch}(L_y),$$
where $w_0$ is the element of maximal length of $W$. Equivalently, the multiplicity of $L_y$ in
$M_w$ is $[M_w : L_y] = P_{w_0 w, w_0 y}(1)$.

Here `cs` is any Coxeter system on the Weyl group whose simple generators are the simple
reflections, `R`, `P` are the (uniquely determined) families of $R$-polynomials and
Kazhdan–Lusztig polynomials of `cs`, and `w₀` is any element of maximal length (there is exactly
one). -/
theorem kazhdan_lusztig_conjectures.parts.ii (b : RootPairing.Base Φ) [Fintype 𝔚]
    {cm : CoxeterMatrix b.support} (cs : CoxeterSystem cm 𝔚)
    (hcs : ∀ i : b.support, cs.simple i = RootPairing.weylGroup.ofIdx Φ i)
    (R P : 𝔚 → 𝔚 → ℤ[X])
    (hR : IsRPolynomials cs R) (hP : IsKazhdanLusztigPolynomials cs R P)
    (w₀ : 𝔚) (hw₀ : ∀ w, cs.length w ≤ cs.length w₀) (w : 𝔚) :
    formalCharacter H (VermaModule b (-(w • weylVector b) - weylVector b)) =
      ∑ y ∈ Finset.univ.filter (fun y => BruhatLE cs y w),
        (P (w₀ * w) (w₀ * y)).eval 1 •
          formalCharacter H
            (SimpleHighestWeightModule b (-(y • weylVector b) - weylVector b)) := by
  sorry

end Conjectures

end KazhdanLusztigConjectures

theorem KazhdanLusztigConjectures.kazhdan_lusztig_conjectures.parts.ii.disproof : ¬ (type_of% @KazhdanLusztigConjectures.kazhdan_lusztig_conjectures.parts.ii) := sorry
