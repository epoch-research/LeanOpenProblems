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
# Nearby Lagrangian conjecture

The *nearby Lagrangian conjecture*, often attributed to Vladimir Arnold, states that any closed
exact Lagrangian submanifold of the cotangent bundle $T^*M$ of a closed manifold $M$ is
Hamiltonian isotopic to the zero section.

Here $T^*M$ carries its canonical symplectic form $\omega = d\lambda$, where $\lambda$ is the
Liouville (or tautological) $1$-form, $\lambda_{(x, \xi)}(v) = \xi(d\pi_{(x, \xi)}(v))$ for
$\pi : T^*M \to M$ the bundle projection. A Lagrangian submanifold $L \subseteq T^*M$ is *exact*
if the restriction $\lambda|_L$ is an exact $1$-form. Two subsets of $T^*M$ are *Hamiltonian
isotopic* if one is the image of the other under the time-one map of the flow of a (compactly
supported) time-dependent Hamiltonian on $T^*M$.

Mathlib has neither cotangent bundles, nor differential forms on manifolds, nor symplectic
structures, so this file introduces the required notions on top of Mathlib's `C^∞` vector
bundles, `mfderiv` and `extDerivWithin`:

- `NearbyLagrangianConjecture.extDerivOneForm I α` is the exterior derivative of a $1$-form `α`
  on a manifold, computed in the extended chart at each point (the same pattern that Mathlib uses
  for `VectorField.mlieBracket`).
- `NearbyLagrangianConjecture.CotangentBundle E M` is the cotangent bundle $T^*M$, realised as the
  total space of the bundle of continuous linear functionals on the tangent spaces of `M`.
- `NearbyLagrangianConjecture.liouvilleForm` is the Liouville $1$-form $\lambda$ on $T^*M$ and
  `NearbyLagrangianConjecture.canonicalSymplecticForm` is $\omega = d\lambda$.
- `NearbyLagrangianConjecture.IsHamiltonianIsotopy φ` says that the smooth family `φ t` of maps of
  $T^*M$ with `φ 0 = id` is the flow of the Hamiltonian vector field of a smooth time-dependent
  Hamiltonian supported in a fixed compact set.
- `NearbyLagrangianConjecture.IsExactLagrangianEmbedding ι` says that a smooth embedding
  `ι : L → T*M` of a manifold `L` of the same dimension as `M` satisfies $\iota^*\omega = 0$ and
  $\iota^*\lambda = df$ for some smooth `f : L → ℝ`.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Nearby_Lagrangian_conjecture)
- [Wikipedia, list of unsolved problems](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
-/

open scoped Manifold ContDiff Bundle
open Bundle Function

namespace NearbyLagrangianConjecture

section ExteriorDerivative

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

/-- The exterior derivative $d\alpha$ of a $1$-form `α` on a manifold `N`, evaluated at `z` on
the tangent vectors `u`, `w`. It is computed in the chart $e = $ `extChartAt I z`: the coordinate
expression of `α` is the $1$-form $\tilde\alpha(y) = \alpha_{e^{-1}(y)} \circ d(e^{-1})_y$ on
the model space, whose exterior derivative (`extDerivWithin`, within the target of $e$) is
evaluated at $e(z)$ on the images of `u`, `w` under $de_z$. For a differentiable `α` and a
boundaryless manifold this does not depend on the chart, by naturality of the exterior
derivative. -/
noncomputable def extDerivOneForm (α : (z : N) → TangentSpace I z →L[ℝ] ℝ) (z : N)
    (u w : TangentSpace I z) : ℝ :=
  extDerivWithin
    (fun y : E ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)
      ((α ((extChartAt I z).symm y)).comp (mfderiv 𝓘(ℝ, E) I (extChartAt I z).symm y)))
    (extChartAt I z).target (extChartAt I z z)
    ![mfderiv I 𝓘(ℝ, E) (extChartAt I z) z u, mfderiv I 𝓘(ℝ, E) (extChartAt I z) z w]

/-- The exterior derivative of a $1$-form vanishes when its first argument is zero. -/
@[category API, AMS 53 58]
theorem extDerivOneForm_zero_left (α : (z : N) → TangentSpace I z →L[ℝ] ℝ) (z : N)
    (w : TangentSpace I z) : extDerivOneForm I α z 0 w = 0 :=
  ContinuousAlternatingMap.map_coord_zero _ 0 (ContinuousLinearMap.map_zero _)

/-- The exterior derivative of a $1$-form is antisymmetric. -/
@[category API, AMS 53 58]
theorem extDerivOneForm_swap (α : (z : N) → TangentSpace I z →L[ℝ] ℝ) (z : N)
    (u w : TangentSpace I z) : extDerivOneForm I α z u w = -extDerivOneForm I α z w u := by
  unfold extDerivOneForm
  rw [← ContinuousAlternatingMap.coe_toAlternatingMap,
    ← AlternatingMap.map_swap _ _ (show (0 : Fin 2) ≠ 1 by decide)]
  congr 1
  ext i
  fin_cases i <;> rfl

end ExteriorDerivative

/-- The exterior derivative of the $1$-form $x\,dy$ on $\mathbb{R}^2$ is $dx \wedge dy$, which
takes the value $1$ on the standard basis $(e_1, e_2)$. -/
@[category test, AMS 53 58]
theorem extDerivOneForm_xdy (z : ℝ × ℝ) :
    extDerivOneForm 𝓘(ℝ, ℝ × ℝ) (fun z : ℝ × ℝ ↦
      (z.1 • ContinuousLinearMap.snd ℝ ℝ ℝ : TangentSpace 𝓘(ℝ, ℝ × ℝ) z →L[ℝ] ℝ))
      z (1, 0) (0, 1) = 1 := by
  have h : ((extChartAt 𝓘(ℝ, ℝ × ℝ) z).symm : ℝ × ℝ → ℝ × ℝ) = id := by
    rw [extChartAt_model_space_eq_id]; rfl
  simp only [extDerivOneForm]
  rw [h]
  simp only [mfderiv_id, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    PartialEquiv.refl_target, id]
  set B := (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ) with hB
  have : (fun y : ℝ × ℝ ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ) ℝ (0 : Fin 1)
      ((y.1 • ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ × ℝ) y)))) =
      fun y : ℝ × ℝ ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ) ℝ (0 : Fin 1) (B y) := by
    funext y
    ext v; rfl
  have hd : DifferentiableAt ℝ (fun y : ℝ × ℝ ↦
      ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ) ℝ (0 : Fin 1) (B y)) z :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ℝ × ℝ) (F := ℝ)
      (0 : Fin 1)).toContinuousLinearEquiv.differentiableAt.comp z B.differentiableAt
  rw [this, extDerivWithin_univ, extDeriv_apply hd]
  simp [Fin.sum_univ_two, hB, Fin.removeNth, Fin.succAbove]
  rw [fderiv_fst]
  rfl

section CotangentBundle

/-- The cotangent bundle $T^*M$ of a manifold `M` modelled on the normed space `E`: the total
space of the bundle whose fibre over `x : M` is the space of continuous linear functionals on the
tangent space of `M` at `x`. -/
abbrev CotangentBundle (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] :=
  TotalSpace (E →L[ℝ] ℝ) (fun x : M => TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ)

/-- The model with corners of the cotangent bundle of a boundaryless manifold modelled on `E`. -/
abbrev cotangentModel (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ModelWithCorners ℝ (E × (E →L[ℝ] ℝ)) (ModelProd E (E →L[ℝ] ℝ)) :=
  𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The Liouville (tautological) $1$-form $\lambda$ on the cotangent bundle $T^*M$: at a point
$p = (x, \xi) \in T^*M$ and for a tangent vector $v \in T_p(T^*M)$, it is given by
$\lambda_p(v) = \xi(d\pi_p(v))$, where $\pi : T^*M \to M$ is the bundle projection. -/
noncomputable def liouvilleForm (p : CotangentBundle E M) :
    TangentSpace (cotangentModel E) p →L[ℝ] ℝ :=
  p.2.comp (mfderiv (cotangentModel E) 𝓘(ℝ, E) TotalSpace.proj p)

/-- The Liouville form vanishes along the zero section of $T^*M$. -/
@[category API, AMS 53 57]
theorem liouvilleForm_zeroSection (x : M) :
    liouvilleForm ((zeroSection _ _ : M → CotangentBundle E M) x) = 0 :=
  ContinuousLinearMap.zero_comp _

/-- The canonical symplectic form $\omega = d\lambda$ on $T^*M$, evaluated at the point `p` on
the tangent vectors `u`, `w`. (Some authors use the opposite sign convention
$\omega = -d\lambda$; this does not affect the notions of Lagrangian submanifold or of
Hamiltonian isotopy.) -/
noncomputable def canonicalSymplecticForm (p : CotangentBundle E M)
    (u w : TangentSpace (cotangentModel E) p) : ℝ :=
  extDerivOneForm (cotangentModel E) liouvilleForm p u w

/-- The canonical symplectic form vanishes when its first argument is zero. -/
@[category API, AMS 53 57]
theorem canonicalSymplecticForm_zero_left (p : CotangentBundle E M)
    (w : TangentSpace (cotangentModel E) p) : canonicalSymplecticForm p 0 w = 0 :=
  extDerivOneForm_zero_left _ _ _ _

/-- A family `φ : ℝ → T*M → T*M` is a (compactly supported) *Hamiltonian isotopy* of $T^*M$ if
it is the flow of a compactly supported time-dependent Hamiltonian: `φ` is jointly smooth,
`φ 0 = id`, and there is a smooth `H : ℝ → T*M → ℝ`, with all `H t` supported in a fixed compact
set, such that for all `t` and `p` the velocity $\partial_t \varphi_t(p)$ is the Hamiltonian
vector field of $H_t$ at $\varphi_t(p)$, i.e. $\omega(\partial_t \varphi_t(p), v) = dH_t(v)$
for all tangent vectors $v$ at $\varphi_t(p)$. (The sign convention for the Hamiltonian vector
field is immaterial: replacing `H` by `-H` interchanges the two conventions.) The time parameter
ranges over all of $\mathbb{R}$ rather than $[0, 1]$; the two conventions are equivalent after
reparametrising time. -/
structure IsHamiltonianIsotopy (φ : ℝ → CotangentBundle E M → CotangentBundle E M) : Prop where
  /-- The isotopy depends smoothly on the time parameter. -/
  contMDiff : ContMDiff (𝓘(ℝ).prod (cotangentModel E)) (cotangentModel E) ∞ (uncurry φ)
  /-- The isotopy starts at the identity. -/
  zero_eq_id : φ 0 = id
  /-- The isotopy is generated by a smooth Hamiltonian supported in a fixed compact set. -/
  exists_hamiltonian : ∃ H : ℝ → CotangentBundle E M → ℝ,
    ContMDiff (𝓘(ℝ).prod (cotangentModel E)) 𝓘(ℝ) ∞ (uncurry H) ∧
    (∃ K : Set (CotangentBundle E M), IsCompact K ∧ ∀ t, ∀ p ∉ K, H t p = 0) ∧
    ∀ t p v, canonicalSymplecticForm (φ t p)
      (mfderiv 𝓘(ℝ) (cotangentModel E) (fun s ↦ φ s p) t 1) v =
        mfderiv (cotangentModel E) 𝓘(ℝ) (H t) (φ t p) v

/-- Two subsets `S`, `T` of $T^*M$ are *Hamiltonian isotopic* if `T` is the image of `S` under
the time-one map of a (compactly supported) Hamiltonian isotopy of $T^*M$. -/
def HamiltonianIsotopic (S T : Set (CotangentBundle E M)) : Prop :=
  ∃ φ, IsHamiltonianIsotopy φ ∧ φ 1 '' S = T

/-- The constant family `id` is a Hamiltonian isotopy, generated by the zero Hamiltonian. -/
@[category test, AMS 53 57]
theorem isHamiltonianIsotopy_id :
    IsHamiltonianIsotopy (fun _ : ℝ ↦ (id : CotangentBundle E M → CotangentBundle E M)) where
  contMDiff := contMDiff_snd
  zero_eq_id := rfl
  exists_hamiltonian :=
    ⟨fun _ _ ↦ 0, contMDiff_const, ⟨∅, isCompact_empty, fun _ _ _ ↦ rfl⟩, fun t p v ↦ by
      simp [mfderiv_const, canonicalSymplecticForm_zero_left]⟩

/-- Every subset of $T^*M$ is Hamiltonian isotopic to itself. -/
@[category API, AMS 53 57]
theorem hamiltonianIsotopic_refl (S : Set (CotangentBundle E M)) : HamiltonianIsotopic S S :=
  ⟨fun _ ↦ id, isHamiltonianIsotopy_id, Set.image_id S⟩

variable {L : Type*} [TopologicalSpace L] [ChartedSpace E L]

/-- A map `ι : L → T*M` from a manifold `L` modelled on the same normed space `E` as `M` (so that
$\dim L = \dim M$) is an *exact Lagrangian embedding* if it is a smooth embedding whose image is
Lagrangian (isotropic, $\iota^*\omega = 0$, and of half the dimension of $T^*M$) and exact, i.e.
$\iota^*\lambda = df$ for some smooth function $f : L \to \mathbb{R}$.

Since $\omega = d\lambda$, the isotropy condition follows from exactness, as
$\iota^*\omega = d(\iota^*\lambda) = d(df) = 0$; it is kept to match the usual definition. -/
structure IsExactLagrangianEmbedding (ι : L → CotangentBundle E M) : Prop where
  /-- `ι` is a smooth embedding. -/
  isSmoothEmbedding : Manifold.IsSmoothEmbedding 𝓘(ℝ, E) (cotangentModel E) ∞ ι
  /-- The image of `ι` is isotropic: $\iota^*\omega = 0$. -/
  isotropic : ∀ (x : L) (v w : TangentSpace 𝓘(ℝ, E) x),
    canonicalSymplecticForm (ι x) (mfderiv 𝓘(ℝ, E) (cotangentModel E) ι x v)
      (mfderiv 𝓘(ℝ, E) (cotangentModel E) ι x w) = 0
  /-- The pull-back $\iota^*\lambda$ of the Liouville form is exact: $\iota^*\lambda = df$ for a
  smooth function `f : L → ℝ`. -/
  exact : ∃ f : L → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f ∧ ∀ x : L,
    (liouvilleForm (ι x)).comp (mfderiv 𝓘(ℝ, E) (cotangentModel E) ι x) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x

/-- The zero section of $T^*M$ is a smooth embedding `M → T*M`. -/
@[category test, AMS 53 57]
theorem isSmoothEmbedding_zeroSection :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, E) (cotangentModel E) ∞
      (zeroSection _ _ : M → CotangentBundle E M) := by
  refine ⟨⟨E →L[ℝ] ℝ, inferInstance, inferInstance, fun x => ?_⟩, ?_⟩
  · refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
      (contMDiff_zeroSection ℝ _ (n := ∞) (IB := 𝓘(ℝ, E))).continuous.continuousAt
      (ContinuousLinearEquiv.refl ℝ _) (chartAt E x)
      (chartAt (ModelProd E (E →L[ℝ] ℝ)) (zeroSection _ _ x)) (mem_chart_source _ _)
      (mem_chart_source _ _) (IsManifold.chart_mem_maximalAtlas _)
      (IsManifold.chart_mem_maximalAtlas _) ?_
    intro u hu
    simp only [FiberBundle.chartedSpace_chartAt, mfld_simps] at hu ⊢
    have hy : (chartAt E x).symm u ∈ (trivializationAt (E →L[ℝ] ℝ)
        (fun x : M => TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) x).baseSet := by
      rw [hom_trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet]
      simp [(chartAt E x).map_target hu]
    simp [Trivialization.zeroSection ℝ _ hy, (chartAt E x).right_inv hu]
  · exact Function.LeftInverse.isEmbedding (f := TotalSpace.proj) (fun x => rfl)
      (FiberBundle.continuous_proj _ _)
      (contMDiff_zeroSection ℝ _ (n := ∞) (IB := 𝓘(ℝ, E))).continuous

end CotangentBundle

/--
**Nearby Lagrangian conjecture.** Let $M$ be a closed (compact, boundaryless, connected) smooth
manifold and let $L \subseteq T^*M$ be a closed exact Lagrangian submanifold of its cotangent
bundle, equipped with the canonical symplectic form $\omega = d\lambda$. Then $L$ is Hamiltonian
isotopic to the zero section: there is a (compactly supported) Hamiltonian isotopy
$\varphi_t$ of $T^*M$ with $\varphi_0 = \mathrm{id}$ and $\varphi_1(0_M) = L$.

Here `M` and `L` are smooth manifolds modelled on the same finite-dimensional space `E` with the
boundaryless model `𝓘(ℝ, E)`, and $L$ is given as the image of an exact Lagrangian embedding
`ι : L → T*M`. Connectedness of `L` follows the usual convention for closed manifolds; in
particular, it excludes the empty submanifold.
-/
@[category research open, AMS 53 57]
theorem nearby_lagrangian_conjecture
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    {L : Type*} [TopologicalSpace L] [ChartedSpace E L] [IsManifold 𝓘(ℝ, E) ∞ L]
    [T2Space L] [CompactSpace L] [ConnectedSpace L]
    (ι : L → CotangentBundle E M) (hι : IsExactLagrangianEmbedding ι) :
    HamiltonianIsotopic (Set.range (zeroSection _ _ : M → CotangentBundle E M)) (Set.range ι) := by
  sorry

end NearbyLagrangianConjecture
