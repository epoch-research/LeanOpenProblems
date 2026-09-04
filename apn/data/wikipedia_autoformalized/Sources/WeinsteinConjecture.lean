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
# Weinstein conjecture

Let $(M, \omega)$ be a symplectic manifold and let $H \colon M \to \mathbb{R}$ be a smooth
Hamiltonian. The Weinstein conjecture asks whether a regular, compact level set $Y = H^{-1}(c)$ of
contact type always carries at least one periodic orbit of the Hamiltonian flow.

Here $Y$ is *of contact type* if there is a $1$-form $\lambda$ on $Y$ with $d\lambda = \omega|_Y$
and $\lambda(v) \neq 0$ for every nonzero $v$ in the characteristic line field
$L_Y = \ker(\omega|_Y) \subseteq TY$. Since $Y$ is compact, this is equivalent to the existence of
a $1$-form $\lambda$ on an open neighbourhood $U$ of $Y$ with $d\lambda = \omega$ on $U$ and
$\lambda(v) \neq 0$ for nonzero $v \in L_Y$ (see McDuff–Salamon, *Introduction to Symplectic
Topology*, Prop. 3.58, or Hofer–Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*,
Section 4.3); this is the formulation used below.

Mathlib has no exterior derivative on manifolds, so we spell out the exterior derivative of
$1$- and $2$-forms through the invariant formulas
$$d\alpha(X, Y) = X(\alpha(Y)) - Y(\alpha(X)) - \alpha([X, Y]),$$
$$d\omega(X, Y, Z) = X(\omega(Y, Z)) - Y(\omega(X, Z)) + Z(\omega(X, Y))
  - \omega([X, Y], Z) + \omega([X, Z], Y) - \omega([Y, Z], X),$$
evaluated on smooth vector fields $X, Y, Z$.

Weinstein's original formulation contained the additional hypothesis $H^1_{dR}(Y) = 0$; this
hypothesis is dropped in the modern form of the conjecture. The conjecture is known for
hypersurfaces in $\mathbb{R}^{2n}$ (Viterbo) and for all closed contact $3$-manifolds (Taubes), but
it is open in general.

*References:*
- [Wikipedia, Weinstein conjecture](https://en.wikipedia.org/wiki/Weinstein_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Ginzburg, *The Weinstein conjecture and the theorems of nearby and almost existence*](https://arxiv.org/abs/math/0310330)
- [Hutchings, *Taubes's proof of the Weinstein conjecture in dimension three*](https://arxiv.org/abs/0906.2444)
- A. Weinstein, *On the hypotheses of Rabinowitz' periodic orbit theorems*, J. Differential
  Equations 33 (1979), 353–358.
-/

namespace WeinsteinConjecture

open scoped Manifold ContDiff
open VectorField Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners ℝ E HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]

variable (I M) in
/-- The smooth (`C^∞`) vector fields on `M`, i.e. the smooth sections of the tangent bundle. -/
abbrev SmoothVectorField := Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯

variable (I M) in
/-- The smooth (`C^∞`) bilinear forms on the tangent bundle of `M`, i.e. the smooth sections of
the bundle of continuous bilinear maps `T_x M → T_x M → ℝ`. A `2`-form is such a section which is
moreover skew-symmetric at every point. -/
abbrev SmoothBilinearForm :=
  Cₛ^∞⟮I; E →L[ℝ] E →L[ℝ] ℝ, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ⟯

variable (I) in
/-- The derivative `X f = df(X)` of a function `f : M → ℝ` along the vector field `X`, at `x`. -/
noncomputable def vectorFieldDeriv (X : Π x : M, TangentSpace I x) (f : M → ℝ) (x : M) : ℝ :=
  mfderiv I 𝓘(ℝ) f x (X x)

/-- On a vector space, `vectorFieldDeriv` is the ordinary directional derivative. -/
@[category API, AMS 53 58]
theorem vectorFieldDeriv_eq_fderiv (X : E → E) (f : E → ℝ) (x : E) :
    vectorFieldDeriv 𝓘(ℝ, E) X f x = fderiv ℝ f x (X x) := by
  simp only [vectorFieldDeriv, mfderiv_eq_fderiv]
  rfl

variable (I) in
/-- The exterior derivative of a `1`-form `α`, evaluated at `x` on the smooth vector fields `X`
and `Y`, via the invariant formula `dα(X, Y) = X(α(Y)) - Y(α(X)) - α([X, Y])`. -/
noncomputable def extDerivOneForm (α : Π x : M, TangentSpace I x →L[ℝ] ℝ)
    (X Y : SmoothVectorField I M) (x : M) : ℝ :=
  vectorFieldDeriv I X (fun y ↦ α y (Y y)) x - vectorFieldDeriv I Y (fun y ↦ α y (X y)) x
    - α x (mlieBracket I X Y x)

/-- The exterior derivative of a `1`-form is antisymmetric in its two arguments. -/
@[category API, AMS 53 58]
theorem extDerivOneForm_swap (α : Π x : M, TangentSpace I x →L[ℝ] ℝ)
    (X Y : SmoothVectorField I M) (x : M) :
    extDerivOneForm I α X Y x = - extDerivOneForm I α Y X x := by
  unfold extDerivOneForm
  rw [mlieBracket_swap_apply (V := Y) (W := X), map_neg]
  ring

variable (I) in
/-- The exterior derivative of a `2`-form `Ω`, evaluated at `x` on the smooth vector fields `X`,
`Y` and `Z`, via the invariant formula
`dΩ(X, Y, Z) = X(Ω(Y, Z)) - Y(Ω(X, Z)) + Z(Ω(X, Y)) - Ω([X, Y], Z) + Ω([X, Z], Y) - Ω([Y, Z], X)`.
-/
noncomputable def extDerivTwoForm (Ω : SmoothBilinearForm I M) (X Y Z : SmoothVectorField I M)
    (x : M) : ℝ :=
  vectorFieldDeriv I X (fun y ↦ Ω y (Y y) (Z y)) x
    - vectorFieldDeriv I Y (fun y ↦ Ω y (X y) (Z y)) x
    + vectorFieldDeriv I Z (fun y ↦ Ω y (X y) (Y y)) x
    - Ω x (mlieBracket I X Y x) (Z x) + Ω x (mlieBracket I X Z x) (Y x)
    - Ω x (mlieBracket I Y Z x) (X x)

/-- A smooth bilinear form `Ω` on the tangent bundle of `M` is a *symplectic form* if it is
skew-symmetric, nondegenerate and closed (`dΩ = 0`). -/
structure IsSymplecticForm (Ω : SmoothBilinearForm I M) : Prop where
  skew : ∀ (x : M) (v w : TangentSpace I x), Ω x v w = - Ω x w v
  nondegenerate : ∀ (x : M) (v : TangentSpace I x), (∀ w : TangentSpace I x, Ω x v w = 0) → v = 0
  closed : ∀ (X Y Z : SmoothVectorField I M) (x : M), extDerivTwoForm I Ω X Y Z x = 0

/-- `X` is the Hamiltonian vector field of `H` with respect to `Ω`: `Ω(X, ·) = dH`. (With the
opposite sign convention `Ω(X, ·) = -dH` one obtains the vector field `-X`, which has the same
periodic orbits.) -/
def IsHamiltonianVectorField (Ω : SmoothBilinearForm I M) (H : M → ℝ)
    (X : Π x : M, TangentSpace I x) : Prop :=
  ∀ (x : M) (v : TangentSpace I x), Ω x (X x) v = mfderiv I 𝓘(ℝ) H x v

/-- The level set `Y = H ⁻¹' {c}` in the symplectic manifold `(M, Ω)` is *of contact type*: there
are an open neighbourhood `U` of `Y` and a `1`-form `α`, smooth on `U`, such that `dα = Ω` on `U`
and `α` does not vanish on the nonzero vectors of the characteristic line field
`ker (Ω|_Y) ⊆ TY`. Here the tangent space `T_x Y` of the (regular) level set at `x ∈ Y` is
`ker dH_x`, so `v ∈ T_x M` lies in `ker (Ω|_Y)` iff `dH_x v = 0` and `Ω_x(v, w) = 0` for all `w`
with `dH_x w = 0`. -/
def IsContactTypeLevelSet (Ω : SmoothBilinearForm I M) (H : M → ℝ) (c : ℝ) : Prop :=
  ∃ (U : Set M) (α : Π x : M, TangentSpace I x →L[ℝ] ℝ), IsOpen U ∧ H ⁻¹' {c} ⊆ U ∧
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (α x)) U ∧
    (∀ x ∈ U, ∀ X Y : SmoothVectorField I M, extDerivOneForm I α X Y x = Ω x (X x) (Y x)) ∧
    ∀ x ∈ H ⁻¹' {c}, ∀ v : TangentSpace I x, v ≠ 0 → mfderiv I 𝓘(ℝ) H x v = 0 →
      (∀ w : TangentSpace I x, mfderiv I 𝓘(ℝ) H x w = 0 → Ω x v w = 0) → α x v ≠ 0

/--
**Weinstein conjecture.** Does a regular compact contact type level set of a Hamiltonian on a
symplectic manifold carry at least one periodic orbit of the Hamiltonian flow?

Precisely: let `(M, Ω)` be a (finite-dimensional, Hausdorff, boundaryless, `C^∞`) symplectic
manifold, let `H : M → ℝ` be a smooth Hamiltonian with Hamiltonian vector field `X`, and let
`c` be a regular value of `H` whose level set `Y = H ⁻¹' {c}` is nonempty, compact and of contact
type (the empty set is trivially compact and regular, so `Y` is required to be nonempty). Then there
is a periodic integral curve `γ : ℝ → M` of `X` (with some period `T > 0`) contained in `Y`.
Such an orbit is automatically non-constant, since `X` has no zeros on the
regular level set `Y`.
-/
@[category research open, AMS 37 53]
theorem weinstein_conjecture :
    answer(sorry) ↔
      ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
        {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners ℝ E HM} [I.Boundaryless]
        {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace HM M] [IsManifold I ∞ M]
        (Ω : SmoothBilinearForm I M) (hΩ : IsSymplecticForm Ω)
        (H : M → ℝ) (hH : ContMDiff I 𝓘(ℝ) ∞ H)
        (X : Π x : M, TangentSpace I x) (hX : IsHamiltonianVectorField Ω H X)
        (c : ℝ) (hne : (H ⁻¹' {c}).Nonempty) (hcpt : IsCompact (H ⁻¹' {c}))
        (hreg : ∀ x ∈ H ⁻¹' {c}, mfderiv I 𝓘(ℝ) H x ≠ 0) (hct : IsContactTypeLevelSet Ω H c),
        ∃ γ : ℝ → M, IsMIntegralCurve γ X ∧ (∃ T > 0, Function.Periodic γ T) ∧
          ∀ t, H (γ t) = c := by
  sorry

end WeinsteinConjecture
