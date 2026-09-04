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
# Bombieri–Lang conjecture

The Bombieri–Lang conjecture predicts that the $K$-rational points of a positive-dimensional
variety of general type over a number field $K$ are not Zariski dense.

Mathlib has no notion of canonical bundle or Kodaira dimension, so this file defines "general
type" from scratch, following the classical description of pluricanonical forms as rational
differential forms. For an integral scheme $X$ over $K$ with function field $F = K(X)$, an
$m$-canonical rational form of degree $n$ is an element of
$(\bigwedge^n_F \Omega_{F/K})^{\otimes m}$. Such a form is regular on a nonempty affine open
$U = \operatorname{Spec} A$ if it is an $A$-linear combination of forms
$(df_{1,1} \wedge \dots \wedge df_{1,n}) \otimes \dots \otimes
(df_{m,1} \wedge \dots \wedge df_{m,n})$
with all $f_{i,j} \in A$. When $X$ is smooth of dimension $n$ over $K$, the forms regular on
every nonempty affine open are exactly the global sections $H^0(X, \omega_X^{\otimes m})$ of the
$m$-th power of the canonical bundle, and their $K$-dimension is the $m$-th plurigenus $P_m(X)$.
A smooth proper variety of dimension $n$ is of general type if its Kodaira dimension is $n$, i.e.
$P_m(X)$ grows like $m^n$. Kodaira dimension is a birational invariant of smooth proper
varieties, and a general variety is of general type if some (equivalently, every) smooth proper
variety birational to it is.

*References:*
- [Wikipedia, Bombieri–Lang conjecture](https://en.wikipedia.org/wiki/Bombieri%E2%80%93Lang_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Kodaira dimension](https://en.wikipedia.org/wiki/Kodaira_dimension)
- [La74] S. Lang, *Higher dimensional diophantine problems*, Bull. Amer. Math. Soc. 80 (1974),
  779–787.
- [Po12] B. Poonen, *Uniform boundedness of rational points and preperiodic points*,
  [arXiv:1206.7104](https://arxiv.org/abs/1206.7104).
- [DT15] P. Das, A. Turchet, *Rational Points, Rational Curves, and Entire Holomorphic Curves on
  Projective Varieties*, Contemp. Math. 654 (2015),
  [arXiv:1407.7750](https://arxiv.org/abs/1407.7750).
-/

namespace BombieriLangConjecture

open CategoryTheory AlgebraicGeometry Filter
open scoped TensorProduct

universe u

variable (K : Type u) [Field K]

/-- The `K`-algebra structure on the function field $K(X)$ of an integral scheme `X` over
`Spec K`, induced by the structure morphism `X ⟶ Spec K`. -/
noncomputable scoped instance functionFieldAlgebra (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [IsIntegral X] : Algebra K X.functionField :=
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  ((Scheme.ΓSpecIso (.of K)).inv ≫ (X ↘ Spec (.of K)).appTop ≫
    X.germToFunctionField ⊤).hom.toAlgebra

/-- The `K`-vector space $(\bigwedge^n_{K(X)} \Omega_{K(X)/K})^{\otimes m}$ of rational
`m`-canonical forms of degree `n` on an integral scheme `X` over `Spec K`, where $K(X)$ is
the function field of `X`. When `X` is smooth of dimension `n` over `K`, this is the generic
fibre of the `m`-th tensor power $\omega_X^{\otimes m}$ of the canonical bundle. -/
abbrev RationalPluricanonicalForm (X : Scheme.{u}) [X.Over (Spec (.of K))] [IsIntegral X]
    (n m : ℕ) : Type u :=
  ⨂[X.functionField]^m (⋀[X.functionField]^n Ω[X.functionField⁄K])

/-- The rational `m`-canonical forms of degree `n` on an integral scheme `X` over `Spec K`
that are *regular* on the nonempty open `U`, meaning that they are
$\Gamma(X, U)$-linear combinations of forms
$(df_{1,1} \wedge \dots \wedge df_{1,n}) \otimes \dots \otimes
(df_{m,1} \wedge \dots \wedge df_{m,n})$ with all $f_{i,j} \in \Gamma(X, U)$.
Since $K$ maps into $\Gamma(X, U)$, this $\Gamma(X, U)$-span is the same as the `K`-span of
the forms $a \cdot (df_{1,1} \wedge \dots \wedge df_{1,n}) \otimes \dots$ with
$a, f_{i,j} \in \Gamma(X, U)$.

This description is the correct one when `U` is affine and `X` is smooth of dimension `n`
over `K`: then it is the space of sections of $\omega_X^{\otimes m}$ over `U`. -/
noncomputable def regularPluricanonicalForms (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [IsIntegral X] (n m : ℕ) (U : X.Opens) [Nonempty U] :
    Submodule K (RationalPluricanonicalForm K X n m) :=
  Submodule.span K {ω | ∃ (a : Γ(X, U)) (f : Fin m → Fin n → Γ(X, U)),
    ω = algebraMap Γ(X, U) X.functionField a •
      ⨂ₜ[X.functionField] i, exteriorPower.ιMulti X.functionField n fun j ↦
        KaehlerDifferential.D K X.functionField (algebraMap Γ(X, U) X.functionField (f i j))}

/-- The rational `m`-canonical forms of degree `n` on an integral scheme `X` over `Spec K`
that are regular on every nonempty affine open of `X`. When `X` is smooth of dimension `n`
over `K`, this is the space of global sections $H^0(X, \omega_X^{\otimes m})$ of the `m`-th
tensor power of the canonical bundle $\omega_X = \bigwedge^n \Omega_{X/K}$. -/
noncomputable def globalPluricanonicalForms (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [IsIntegral X] (n m : ℕ) : Submodule K (RationalPluricanonicalForm K X n m) :=
  ⨅ (U : X.Opens) (_ : IsAffineOpen U) (_ : Nonempty U), regularPluricanonicalForms K X n m U

/-- The `m`-th *plurigenus* $P_m(X) = \dim_K H^0(X, \omega_X^{\otimes m})$ of an integral
scheme `X` over `Spec K`, computed with forms of degree `n`. This is the classical plurigenus
when `X` is smooth and proper of dimension `n` over `K` (in which case
$H^0(X, \omega_X^{\otimes m})$ is finite-dimensional). -/
noncomputable def plurigenus (X : Scheme.{u}) [X.Over (Spec (.of K))] [IsIntegral X]
    (n m : ℕ) : ℕ :=
  Module.finrank K (globalPluricanonicalForms K X n m)

/-- Two schemes `X` and `Y` over `Spec K` are *birational* over `K` if they contain dense open
subschemes that are isomorphic as `K`-schemes. -/
def IsBirational (X Y : Scheme.{u}) [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))] : Prop :=
  ∃ (U : X.Opens) (V : Y.Opens) (e : (U : Scheme.{u}) ≅ V),
    Dense (U : Set X) ∧ Dense (V : Set Y) ∧
    (e.hom ≫ (V.ι ≫ (Y ↘ Spec (.of K)))) = (U.ι ≫ (X ↘ Spec (.of K)))

/-- A smooth proper integral scheme `X` of dimension `n` over `Spec K` is *of general type* if
its Kodaira dimension $\kappa(X)$ equals `n`, i.e. if its plurigenera $P_m(X)$ grow like
$m^n$: there is a constant $c > 0$ with $m^n \le c \cdot P_m(X)$ for infinitely many `m`.

(By Iitaka's theorem, $P_m(X) = O(m^{\kappa(X)})$, and $P_m(X) \ge a m^{\kappa(X)}$ for all
large `m` in the semigroup of `m` with $P_m(X) \ne 0$, so this is equivalent to
$\kappa(X) = n$.) -/
def IsSmoothProperOfGeneralType (X : Scheme.{u}) [X.Over (Spec (.of K))] [IsIntegral X]
    (n : ℕ) : Prop :=
  IsProper (X ↘ Spec (.of K)) ∧ IsSmoothOfRelativeDimension n (X ↘ Spec (.of K)) ∧
    ∃ c : ℕ, 0 < c ∧ ∃ᶠ m in atTop, m ^ n ≤ c * plurigenus K X n m

/-- An integral scheme `X` over `Spec K` is *of general type* if it is birational over `K` to
a smooth proper integral `K`-scheme `X'` of some dimension `n` with Kodaira dimension
$\kappa(X') = n$. Since the Kodaira dimension is a birational invariant of smooth proper
varieties, the choice of `X'` does not matter. -/
def IsGeneralType (X : Scheme.{u}) [X.Over (Spec (.of K))] : Prop :=
  ∃ (X' : Scheme.{u}) (_ : X'.Over (Spec (.of K))) (_ : IsIntegral X') (n : ℕ),
    IsBirational K X X' ∧ IsSmoothProperOfGeneralType K X' n

/-- The set of `K`-rational points of a scheme `X` over `Spec K`, viewed as a subset of the
underlying (Zariski) topological space of `X`: the images of the `K`-morphisms
`Spec K ⟶ X`. -/
def rationalPoints (X : Scheme.{u}) [X.Over (Spec (.of K))] : Set X :=
  {x | ∃ p : Spec (.of K) ⟶ X, (p ≫ (X ↘ Spec (.of K))) = 𝟙 _ ∧ p.base default = x}

/-- **Bombieri–Lang conjecture.** Let $K$ be a number field and let $X$ be a positive-dimensional
variety (an integral separated scheme of finite type over $K$) of general type over $K$. Then
the set $X(K)$ of $K$-rational points of $X$ is not dense in the Zariski topology on $X$.

The positive-dimensionality hypothesis excludes the point $\operatorname{Spec} K$, which is of
general type with trivially dense rational points. -/
theorem bombieri_lang_conjecture [NumberField K] (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [IsIntegral X] [IsSeparated (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] (hdim : 0 < topologicalKrullDim X)
    (hX : IsGeneralType K X) :
    ¬ Dense (rationalPoints K X) := by
  sorry

end BombieriLangConjecture

theorem BombieriLangConjecture.bombieri_lang_conjecture.disproof : ¬ (type_of% @BombieriLangConjecture.bombieri_lang_conjecture) := sorry
