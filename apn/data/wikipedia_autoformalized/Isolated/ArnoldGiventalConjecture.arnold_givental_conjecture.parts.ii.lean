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
# Arnold–Givental conjecture and Arnold conjecture

The *Arnold conjecture* bounds from below the number of fixed points of a Hamiltonian
diffeomorphism of a closed symplectic manifold $(M, ω)$ by Morse-theoretic invariants of $M$:
the minimal number of critical points of a smooth function on $M$ (strong form), the minimal number
of critical points of a Morse function on $M$ (nondegenerate form), or the sum of the Betti numbers
of $M$ (weak form).

The *Arnold–Givental conjecture* bounds from below the number of transverse intersection points
of a compact Lagrangian submanifold $L$, which is the fixed point set of an anti-symplectic
involution, with its image under a Hamiltonian diffeomorphism, by the sum of the $ℤ/2$-Betti
numbers of $L$.

This file introduces the required notions on top of Mathlib's smooth manifolds: symplectic forms
(fields of continuous alternating bilinear forms on the tangent spaces which are smooth and closed
in charts, and nondegenerate), time-dependent Hamiltonian flows, Hamiltonian diffeomorphisms,
nondegenerate diffeomorphisms, critical points, Morse functions, and Betti numbers via Mathlib's
singular homology. Time-dependent Hamiltonians are taken to be smooth functions on `ℝ × M`; the
time-one maps of their flows are exactly the time-one maps of smooth families indexed by `[0, 1]`
(reparametrise the time variable).

*References:*
- [Wikipedia, Arnold–Givental conjecture](https://en.wikipedia.org/wiki/Arnold%E2%80%93Givental_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Fr04] Frauenfelder, U. *The Arnold–Givental conjecture and moment Floer homology*.
  International Mathematics Research Notices (2004).
  [arXiv:math/0309373](https://arxiv.org/abs/math/0309373)
- [RG17] Dimitroglou Rizell, G. and Golovko, R. *The number of Hamiltonian fixed points on
  symplectically aspherical manifolds*. [arXiv:1609.04776](https://arxiv.org/abs/1609.04776)
-/

namespace ArnoldGiventalConjecture

open scoped Manifold EuclideanGeometry
open Manifold Function

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- A (not necessarily smooth) differential `2`-form on `M`: a continuous alternating bilinear
form on each tangent space `T_x M`. -/
abbrev TwoForm := ∀ x : M, TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ

variable {I M}

/-- The local representative of a `2`-form `ω` in the extended chart at `x₀`: the pullback of
`ω` along `(extChartAt I x₀).symm`, a `2`-form on the model space `E`. -/
noncomputable def TwoForm.localRep (ω : TwoForm I M) (x₀ : M) (y : E) :
    E [⋀^Fin 2]→L[ℝ] ℝ :=
  (ω ((extChartAt I x₀).symm y)).compContinuousLinearMap
    (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (Set.range I) y)

/-- A `2`-form `ω` on `M` is a **symplectic form** if it is smooth, closed and nondegenerate.
Smoothness and closedness (`dω = 0`) are expressed through the local representatives of `ω` in
the extended charts at each point, using Mathlib's exterior derivative `extDerivWithin` on the
model space. -/
structure IsSymplecticForm (ω : TwoForm I M) : Prop where
  contDiffWithinAt : ∀ x₀ : M,
    ContDiffWithinAt ℝ ∞ (ω.localRep x₀) (Set.range I) (extChartAt I x₀ x₀)
  closed : ∀ x₀ : M, extDerivWithin (ω.localRep x₀) (Set.range I) (extChartAt I x₀ x₀) = 0
  nondegenerate : ∀ (x : M) (v : TangentSpace I x), (∀ w, ω x ![v, w] = 0) → v = 0

/-- `φ : ℝ → M → M` is the **Hamiltonian flow** of the time-dependent Hamiltonian
`H : ℝ → M → ℝ` with respect to the `2`-form `ω`: `H` is smooth (jointly in time and space),
`φ 0 = id`, and for every `x` the curve `t ↦ φ t x` solves `∂ₜ φ t x = X_{H t} (φ t x)`, where
the Hamiltonian vector field `X_{H t}` is characterised by `ω (X_{H t}, ·) = d (H t)`. -/
def IsHamiltonianFlow (ω : TwoForm I M) (H : ℝ → M → ℝ) (φ : ℝ → M → M) : Prop :=
  ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (uncurry H) ∧ φ 0 = id ∧
    ∀ (t : ℝ) (x : M), ∃ v : TangentSpace I (φ t x),
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s ↦ φ s x) t ((1 : ℝ →L[ℝ] ℝ).smulRight v) ∧
        ∀ w : TangentSpace I (φ t x), ω (φ t x) ![v, w] = mfderiv I 𝓘(ℝ, ℝ) (H t) (φ t x) w

/-- A map `φ : M → M` is a **Hamiltonian diffeomorphism** of `(M, ω)` if it is the time-one map
of the Hamiltonian flow of some (time-dependent) Hamiltonian `H : ℝ → M → ℝ`. -/
def IsHamiltonianDiffeomorph (ω : TwoForm I M) (φ : M → M) : Prop :=
  ∃ (H : ℝ → M → ℝ) (ψ : ℝ → M → M), IsHamiltonianFlow ω H ψ ∧ ψ 1 = φ

variable (I)

/-- A map `φ : M → M` is **nondegenerate** if its graph intersects the diagonal of `M × M`
transversely, i.e. `1` is not an eigenvalue of `dφ_x` at any fixed point `x` of `φ`. -/
def IsNondegenerate (φ : M → M) : Prop :=
  ∀ x ∈ fixedPoints φ, ∀ v : TangentSpace I x,
    (mfderiv I I φ x v : TangentSpace I x) = v → v = 0

/-- The set of critical points of `f : M → ℝ`: the points where the differential of `f`
vanishes. -/
def critPts (f : M → ℝ) : Set M := {x | mfderiv I 𝓘(ℝ, ℝ) f x = 0}

/-- A smooth function `f : M → ℝ` is a **Morse function** if all its critical points are
nondegenerate, i.e. at every critical point `x` the Hessian of `f` (computed in the extended chart
at `x`, which is legitimate since `x` is a critical point) is a nondegenerate bilinear form. -/
def IsMorseFunction (f : M → ℝ) : Prop :=
  ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ ∀ x ∈ critPts I f, ∀ v : E,
    fderivWithin ℝ (fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)) (Set.range I)
      (extChartAt I x x) v = 0 → v = 0

variable (M)

/-- The minimal number of critical points of a smooth function `M → ℝ`. -/
noncomputable def critNumber : ℕ∞ :=
  ⨅ f : {f : M → ℝ // ContMDiff I 𝓘(ℝ, ℝ) ∞ f}, (critPts I f.1).encard

/-- The **Morse number** of `M`: the minimal number of critical points of a Morse function on
`M`. -/
noncomputable def morseNumber : ℕ∞ :=
  ⨅ f : {f : M → ℝ // IsMorseFunction I f}, (critPts I f.1).encard

end Definitions

/-- The `i`-th Betti number of a topological space `X` with coefficients in a field `F`: the
dimension of the `i`-th singular homology of `X` with coefficients in `F`. -/
noncomputable def bettiNumber (F : Type) [Field F] (i : ℕ) (X : Type) [TopologicalSpace X] :
    ℕ :=
  Module.finrank F
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat F) i).obj (ModuleCat.of F F)).obj
      (TopCat.of X))

section API

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

end API

section Conjectures

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ^(2 * n)) M]
  [IsManifold (𝓡 (2 * n)) ∞ M] [T2Space M] [CompactSpace M]

/-- **Arnold conjecture** (strong form). Let $(M, ω)$ be a closed symplectic manifold. The number
of fixed points of a Hamiltonian diffeomorphism of $M$ is greater than or equal to the number of
critical points of a smooth function on $M$, i.e. to the minimal number of critical points of a
smooth function $M → ℝ$. -/
theorem arnold_givental_conjecture.parts.ii
    (ω : TwoForm (𝓡 (2 * n)) M) (hω : IsSymplecticForm ω)
    (φ : M → M) (hφ : IsHamiltonianDiffeomorph ω φ) :
    critNumber (𝓡 (2 * n)) M ≤ (fixedPoints φ).encard := by
  sorry

end Conjectures

end ArnoldGiventalConjecture

theorem ArnoldGiventalConjecture.arnold_givental_conjecture.parts.ii.disproof : ¬ (type_of% @ArnoldGiventalConjecture.arnold_givental_conjecture.parts.ii) := sorry
