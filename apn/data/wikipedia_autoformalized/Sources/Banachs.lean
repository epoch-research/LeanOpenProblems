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
# Banach's problem

Is there an ergodic system with simple Lebesgue spectrum?

The problem goes back to Banach and is recorded in Ulam's *A Collection of Mathematical
Problems*: does there exist a square integrable function $f$ and a measure-preserving
transformation $T$ such that the functions $f \circ T^n$ form a complete orthonormal system?

In its modern form the question asks whether there is an ergodic automorphism $T$ of a standard
probability space $(X, \mu)$ whose Koopman operator $U_T f = f \circ T$, restricted to the
orthocomplement $L^2_0(\mu)$ of the constants, has simple Lebesgue spectrum, i.e. its maximal
spectral type is Lebesgue measure on the circle and its multiplicity is one. Equivalently, the
restriction of $U_T$ to $L^2_0(\mu)$ is unitarily equivalent to multiplication by $z$ on
$L^2(\mathbb{T}, \mathrm{Leb})$, i.e. there is $f \in L^2_0(\mu)$ such that
$\{U_T^n f : n \in \mathbb{Z}\}$ is an orthonormal basis of $L^2_0(\mu)$.

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Stefan Banach](https://en.wikipedia.org/wiki/Stefan_Banach)
- S. M. Ulam, *A Collection of Mathematical Problems*, Interscience Publishers, New York, 1960.
- M. Lemańczyk, *Spectral theory of dynamical systems*, in: Encyclopedia of Complexity and
  Systems Science, Springer, 2009.
-/

open MeasureTheory

namespace Banachs

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The **Koopman operator** `f ↦ f ∘ T` on `L²(μ)` associated to a measure-preserving
measurable equivalence `T`, as a unitary operator (a linear isometric equivalence). Its inverse
is `f ↦ f ∘ T⁻¹`. -/
noncomputable def koopman (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toLinearEquiv :=
    { Lp.compMeasurePreservingₗ ℂ T hT with
      invFun := Lp.compMeasurePreservingₗ ℂ T.symm hT.symm
      left_inv := fun f => Lp.ext <|
        (Lp.coeFn_compMeasurePreserving _ hT.symm).trans <|
          (hT.symm.quasiMeasurePreserving.ae_eq_comp
            (Lp.coeFn_compMeasurePreserving f hT)).trans <|
          Filter.EventuallyEq.of_eq <| by
            rw [Function.comp_assoc, MeasurableEquiv.self_comp_symm, Function.comp_id]
      right_inv := fun f => Lp.ext <|
        (Lp.coeFn_compMeasurePreserving _ hT).trans <|
          (hT.quasiMeasurePreserving.ae_eq_comp
            (Lp.coeFn_compMeasurePreserving f hT.symm)).trans <|
          Filter.EventuallyEq.of_eq <| by
            rw [Function.comp_assoc, MeasurableEquiv.symm_comp_self, Function.comp_id] }
  norm_map' f := Lp.norm_compMeasurePreserving f hT

@[category API, AMS 28 37]
lemma koopman_apply (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) (f : Lp ℂ 2 μ) :
    koopman T hT f =ᵐ[μ] f ∘ T :=
  Lp.coeFn_compMeasurePreserving f hT

@[category API, AMS 28 37]
lemma koopman_symm_apply (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) (f : Lp ℂ 2 μ) :
    (koopman T hT).symm f =ᵐ[μ] f ∘ T.symm :=
  Lp.coeFn_compMeasurePreserving f hT.symm

@[category API, AMS 28 37]
lemma koopman_refl_apply (f : Lp ℂ 2 μ) :
    koopman (MeasurableEquiv.refl X) (MeasurePreserving.id μ) f = f :=
  Lp.ext (Lp.coeFn_compMeasurePreserving f (MeasurePreserving.id μ))

/-- A measure-preserving measurable equivalence `T` of a finite measure space `(X, μ)` has
**simple Lebesgue spectrum** (on the orthocomplement of the constants) if there is
`f ∈ L²(μ)` such that the two-sided orbit `{U_T ^ n f : n ∈ ℤ}` of `f` under the Koopman
operator `U_T` is an orthonormal basis of the closed subspace `L²₀(μ) = {1}ᗮ` of `L²(μ)`
orthogonal to the constant functions (necessarily `f ∈ L²₀(μ)`). This is equivalent to the
restriction of `U_T` to `L²₀(μ)` being unitarily equivalent to the bilateral shift, i.e. to
multiplication by `z` on `L²(𝕋, Leb)`: its maximal spectral type is Lebesgue measure and its
spectral multiplicity is one. -/
def HasSimpleLebesgueSpectrum [IsFiniteMeasure μ] (T : X ≃ᵐ X)
    (hT : MeasurePreserving T μ μ) : Prop :=
  ∃ f : Lp ℂ 2 μ,
    Orthonormal ℂ (fun n : ℤ => (koopman T hT ^ n) f) ∧
    (Submodule.span ℂ (Set.range fun n : ℤ => (koopman T hT ^ n) f)).topologicalClosure =
      (ℂ ∙ Lp.const 2 μ (1 : ℂ))ᗮ

/-- The identity transformation does not have simple Lebesgue spectrum: the Koopman orbit of any
`f` is constant, so it cannot be orthonormal. -/
@[category test, AMS 28 37]
lemma not_hasSimpleLebesgueSpectrum_refl [IsFiniteMeasure μ] :
    ¬ HasSimpleLebesgueSpectrum (MeasurableEquiv.refl X) (MeasurePreserving.id μ) := by
  rintro ⟨f, hf, -⟩
  have h1 := hf.1 0
  have h0 := hf.inner_eq_zero (zero_ne_one : (0 : ℤ) ≠ 1)
  simp only [zpow_zero, zpow_one, LinearIsometryEquiv.coe_one, id_eq, koopman_refl_apply,
    inner_self_eq_zero] at h0 h1
  simp [h0] at h1

/-- **Banach's problem.** Is there an ergodic system with simple Lebesgue spectrum?

That is, is there an ergodic invertible measure-preserving transformation `T` of a standard
Borel probability space `(X, μ)` whose Koopman operator `U_T f = f ∘ T`, restricted to the
orthocomplement `L²₀(μ)` of the constants, has simple Lebesgue spectrum: there is
`f ∈ L²₀(μ)` such that `{f ∘ Tⁿ : n ∈ ℤ}` is an orthonormal basis of `L²₀(μ)`?

The spectrum is taken on `L²₀(μ)` because the constant functions are always eigenfunctions of
`U_T` with eigenvalue `1`, so `U_T` itself never has Lebesgue spectrum on all of `L²(μ)`. -/
@[category research open, AMS 28 37 47]
theorem banachs :
    answer(sorry) ↔
      ∃ (X : Type) (_ : MeasurableSpace X) (_ : StandardBorelSpace X) (μ : Measure X)
        (_ : IsProbabilityMeasure μ) (T : X ≃ᵐ X) (hT : Ergodic T μ),
        HasSimpleLebesgueSpectrum T hT.toMeasurePreserving := by
  sorry

end Banachs
