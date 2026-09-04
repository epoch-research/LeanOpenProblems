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
# Fujita conjecture

Let $M$ be a compact complex manifold of complex dimension $n$, let $L$ be a positive
(equivalently, by the Kodaira embedding theorem, ample) holomorphic line bundle on $M$ and let
$K_M$ be the canonical line bundle of $M$. Fujita's conjecture states that the line bundle
$K_M \otimes L^{\otimes m}$ is
* spanned by (global holomorphic) sections when $m \geq n + 1$;
* very ample when $m \geq n + 2$.

The notions involved are formulated for holomorphic line bundles over a complex manifold `M`
modelled on a complex normed space via `I : ModelWithCorners ℂ EM HM` (in the conjecture itself,
`I = 𝓘(ℂ, EuclideanSpace ℂ (Fin n))`):
* a holomorphic line bundle is a vector bundle `E : M → Type*` with model fibre `ℂ` whose
  changes of trivialisation are complex analytic (`ContMDiffVectorBundle ω ℂ E I`), and its
  holomorphic sections are the complex analytic sections `Cₛ^ω⟮I; ℂ, E⟯`;
* a line bundle is *spanned by sections* if its global holomorphic sections span every fibre;
* a line bundle is *very ample* if its global holomorphic sections span every fibre, separate
  points and separate tangent vectors; for compact `M` this says exactly that the global
  holomorphic sections define a holomorphic embedding of `M` into a projective space;
* a line bundle is *ample* if some positive tensor power is very ample; on a compact complex
  manifold this is equivalent to positivity by the Kodaira embedding theorem;
* since Mathlib has no tensor products or exterior powers of vector bundles, the bundle
  $K_M \otimes L^{\otimes m}$ is characterised up to isomorphism: `IsAdjointBundle I L m E` says
  that `E` carries a holomorphic fibrewise multiplication
  $\Lambda^n T_x^*M \times L_x^m \to E_x$ which is nonzero on nonzero pure tensors, i.e. that
  `E` is isomorphic to $K_M \otimes L^{\otimes m}$. The conjecture is stated for every such `E`.

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Fujita_conjecture)
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* T. Fujita, *On polarized manifolds whose adjoint bundles are not semipositive*,
  Algebraic geometry, Sendai, 1985, Adv. Stud. Pure Math. 10 (1987), 167–178.
  [doi:10.2969/aspm/01010167](https://doi.org/10.2969/aspm/01010167)
* L. Ein, R. Lazarsfeld, *Global generation of pluricanonical and adjoint linear series on smooth
  projective threefolds*, J. Amer. Math. Soc. 6 (1993), 875–903.
  [doi:10.1090/S0894-0347-1993-1207013-5](https://doi.org/10.1090/S0894-0347-1993-1207013-5)
-/

namespace FujitaConjecture

open Bundle Function
open scoped Manifold ContDiff

universe u v

variable {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℂ EM] [TopologicalSpace HM]
  (I : ModelWithCorners ℂ EM HM) {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-- A local section `s` of a vector bundle `V` (with model fibre `F`) over the complex manifold
`M` is *holomorphic on* the set `U` if it is complex analytic on `U`. -/
def IsHolomorphicSectionOn (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    (V : M → Type*) [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
    [FiberBundle F V] (s : ∀ x, V x) (U : Set M) : Prop :=
  ContMDiffOn I (I.prod 𝓘(ℂ, F)) ω (fun x ↦ TotalSpace.mk' F x (s x)) U

/-- The holomorphic cotangent bundle of the complex manifold `M`: the fibre at `x` is the dual of
the holomorphic tangent space at `x`. -/
abbrev CotangentSpace (x : M) : Type _ := TangentSpace I x →L[ℂ] Trivial M ℂ x

section LineBundle

variable (E : M → Type u) [TopologicalSpace (TotalSpace ℂ E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle ℂ E]

/-- A holomorphic line bundle `E` is *spanned by sections* (globally generated, base point free)
if for every point `x` the evaluation map from the space of global holomorphic sections of `E`
to the fibre `E x` is surjective. -/
def IsGloballyGenerated : Prop :=
  ∀ x, Surjective fun s : Cₛ^ω⟮I; ℂ, E⟯ ↦ s x

/-- The global holomorphic sections of `E` *separate points* if for any two distinct points
`x ≠ y` the evaluation map to `E x × E y` is surjective. -/
def SeparatesPoints : Prop :=
  ∀ x y, x ≠ y → Surjective fun s : Cₛ^ω⟮I; ℂ, E⟯ ↦ (s x, s y)

/-- The derivative at `x` of the holomorphic section `s` of `E`, computed in the trivialisation
`trivializationAt ℂ E x` of `E` around `x`. When `s x = 0`, changing the holomorphic
trivialisation multiplies this element of the cotangent space $T_x^*M$ by a nonzero scalar: it is
the image of `s` in $\mathfrak{m}_x E_x / \mathfrak{m}_x^2 E_x \cong T_x^*M \otimes E_x$, read
through the identification $E_x \cong \mathbb{C}$ given by the trivialisation. Hence its kernel,
and the span of such derivatives, are intrinsic. -/
noncomputable def localDerivAt (x : M) (s : Cₛ^ω⟮I; ℂ, E⟯) : CotangentSpace I x :=
  mfderiv I 𝓘(ℂ) (fun y ↦ (trivializationAt ℂ E x (TotalSpace.mk' ℂ y (s y))).2) x

/-- The global holomorphic sections of `E` *separate tangent vectors* if for every point `x`
the derivatives at `x` of the global holomorphic sections vanishing at `x` span the whole
cotangent space $T_x^*M$, i.e. the global sections vanishing at `x` span
$\mathfrak{m}_x E_x / \mathfrak{m}_x^2 E_x$. -/
def SeparatesTangentVectors : Prop :=
  ∀ x, Surjective fun s : {s : Cₛ^ω⟮I; ℂ, E⟯ // s x = 0} ↦ localDerivAt I E x s.1

/-- A holomorphic line bundle `E` on `M` is *very ample* if its global holomorphic sections span
every fibre, separate points and separate tangent vectors. For a compact complex manifold `M`
this is equivalent to the classical definition: the global holomorphic sections of `E` define a
holomorphic embedding of `M` into a projective space $\mathbb{P}^N$ under which `E` is the
pullback of $\mathcal{O}(1)$. -/
def IsVeryAmple : Prop :=
  IsGloballyGenerated I E ∧ SeparatesPoints I E ∧ SeparatesTangentVectors I E

end LineBundle

section TensorPowers

variable (L : M → Type v) [TopologicalSpace (TotalSpace ℂ L)] [∀ x, AddCommGroup (L x)]
  [∀ x, Module ℂ (L x)] [∀ x, TopologicalSpace (L x)] [FiberBundle ℂ L]

/-- `IsTensorPower I L k P` says that the holomorphic line bundle `P` is (isomorphic to) the
`k`-th tensor power $L^{\otimes k}$ of the holomorphic line bundle `L`. This is witnessed by a
fibrewise `k`-multilinear multiplication map $\mu_x \colon L_x^k \to P_x$ which is nonzero on
nonzero pure tensors (so that it induces an isomorphism $L_x^{\otimes k} \cong P_x$ of
one-dimensional spaces) and which is holomorphic, in the sense that it maps holomorphic local
sections of `L` to a holomorphic local section of `P`. -/
def IsTensorPower (k : ℕ) (P : M → Type*) [TopologicalSpace (TotalSpace ℂ P)]
    [∀ x, AddCommGroup (P x)] [∀ x, Module ℂ (P x)] [∀ x, TopologicalSpace (P x)]
    [FiberBundle ℂ P] : Prop :=
  ∃ μ : ∀ x, MultilinearMap ℂ (fun _ : Fin k ↦ L x) (P x),
    (∀ x (l : Fin k → L x), (∀ i, l i ≠ 0) → μ x l ≠ 0) ∧
    ∀ (U : Set M), IsOpen U → ∀ s : Fin k → ∀ x, L x,
      (∀ i, IsHolomorphicSectionOn I ℂ L (s i) U) →
      IsHolomorphicSectionOn I ℂ P (fun x ↦ μ x fun i ↦ s i x) U

/-- A holomorphic line bundle `L` on `M` is *ample* if some positive tensor power
$L^{\otimes k}$ is very ample. On a compact complex manifold this is equivalent, by the Kodaira
embedding theorem, to `L` being *positive*, i.e. admitting a hermitian metric whose Chern
curvature form is positive definite. -/
def IsAmple : Prop :=
  ∃ k, 0 < k ∧ ∃ (P : M → Type v) (_ : TopologicalSpace (TotalSpace ℂ P))
    (_ : ∀ x, AddCommGroup (P x)) (_ : ∀ x, Module ℂ (P x)) (_ : ∀ x, TopologicalSpace (P x))
    (_ : FiberBundle ℂ P) (_ : VectorBundle ℂ ℂ P) (_ : ContMDiffVectorBundle ω ℂ P I),
    IsTensorPower I L k P ∧ IsVeryAmple I P

variable [IsManifold I ω M]

/-- `IsAdjointBundle I L m E` says that the holomorphic line bundle `E` is (isomorphic to) the
adjoint bundle $K_M \otimes L^{\otimes m}$, where $K_M = \Lambda^n T^*M$ is the canonical line
bundle of the complex manifold `M` of dimension `n = Module.finrank ℂ EM`. This is witnessed by
a fibrewise multiplication map $\Phi_x \colon (T_x^*M)^n \times L_x^m \to E_x$ which is
alternating in the `n` cotangent vectors and multilinear in the `m` elements of `L_x`, which is
nonzero on nonzero pure tensors (i.e. whenever the cotangent vectors are linearly independent and
the elements of `L_x` are nonzero, so that it induces an isomorphism
$\Lambda^n T_x^*M \otimes L_x^{\otimes m} \cong E_x$ of one-dimensional spaces), and which is
holomorphic, in the sense that it maps holomorphic local `1`-forms and holomorphic local sections
of `L` to a holomorphic local section of `E`. -/
def IsAdjointBundle (m : ℕ) (E : M → Type u) [TopologicalSpace (TotalSpace ℂ E)]
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle ℂ E] : Prop :=
  ∃ Φ : ∀ x, CotangentSpace I x [⋀^Fin (Module.finrank ℂ EM)]→ₗ[ℂ]
      MultilinearMap ℂ (fun _ : Fin m ↦ L x) (E x),
    (∀ x (ξ : Fin (Module.finrank ℂ EM) → CotangentSpace I x) (l : Fin m → L x),
      LinearIndependent ℂ ξ → (∀ i, l i ≠ 0) → Φ x ξ l ≠ 0) ∧
    ∀ (U : Set M), IsOpen U →
      ∀ (ξ : Fin (Module.finrank ℂ EM) → ∀ x, CotangentSpace I x) (s : Fin m → ∀ x, L x),
      (∀ i, IsHolomorphicSectionOn I (EM →L[ℂ] ℂ) (CotangentSpace I) (ξ i) U) →
      (∀ i, IsHolomorphicSectionOn I ℂ L (s i) U) →
      IsHolomorphicSectionOn I ℂ E (fun x ↦ Φ x (fun i ↦ ξ i x) fun i ↦ s i x) U

end TensorPowers

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [CompactSpace M] [T2Space M]
  (L : M → Type v) [TopologicalSpace (TotalSpace ℂ L)] [∀ x, AddCommGroup (L x)]
  [∀ x, Module ℂ (L x)] [∀ x, TopologicalSpace (L x)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]
  [ContMDiffVectorBundle ω ℂ L 𝓘(ℂ, EuclideanSpace ℂ (Fin n))]
  (E : M → Type u) [TopologicalSpace (TotalSpace ℂ E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]
  [ContMDiffVectorBundle ω ℂ E 𝓘(ℂ, EuclideanSpace ℂ (Fin n))]

/-- **Fujita conjecture, part (ii)** (very ampleness): let `M` be a compact complex manifold of
complex dimension `n`, let `L` be a positive (equivalently, ample) holomorphic line bundle on `M`
and let $K_M$ be the canonical line bundle of `M`. Then for every `m ≥ n + 2` the line bundle
$K_M \otimes L^{\otimes m}$ is very ample.

Here `E` is any holomorphic line bundle isomorphic to $K_M \otimes L^{\otimes m}$, see
`IsAdjointBundle`. -/
theorem fujita_conjecture.parts.ii (hL : IsAmple 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) L)
    (m : ℕ) (hm : n + 2 ≤ m) (hE : IsAdjointBundle 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) L m E) :
    IsVeryAmple 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) E := by
  sorry

end FujitaConjecture

theorem FujitaConjecture.fujita_conjecture.parts.ii.disproof : ¬ (type_of% @FujitaConjecture.fujita_conjecture.parts.ii) := sorry
