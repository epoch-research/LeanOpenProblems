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
# Halperin conjecture

Suppose that $F \to E \to B$ is a fibration of simply connected spaces such that $F$ is
rationally elliptic (both $H_*(F; \mathbb{Q})$ and $\pi_*(F) \otimes \mathbb{Q}$ are
finite-dimensional) and $\chi(F) \neq 0$ (i.e. $F$ has non-zero Euler characteristic). Then the
Serre spectral sequence associated to the fibration collapses at the $E_2$ page.

Here the Serre spectral sequence is the one for cohomology with rational coefficients. Its
collapse at $E_2$ is equivalent to the fibration being *totally non-cohomologous to zero* (TNCZ),
i.e. to the fibre inclusion $j \colon F \to E$ inducing a surjection
$j^* \colon H^*(E; \mathbb{Q}) \to H^*(F; \mathbb{Q})$ (see [Lu97], §1). Since $\mathbb{Q}$ is a
field, $H^n(-; \mathbb{Q})$ is the linear dual of $H_n(-; \mathbb{Q})$, so this is in turn
equivalent to the injectivity of $j_* \colon H_n(F; \mathbb{Q}) \to H_n(E; \mathbb{Q})$ in every
degree $n$. This is the form in which the conjecture is stated below, using Mathlib's singular
homology `AlgebraicTopology.singularHomologyFunctor` with rational coefficients.

"Fibration" means Serre fibration, and the fibre is $F = p^{-1}(b)$ for a point $b$ of the base.
[Lu97] works with simply connected CW complexes of finite rational type; following the Wikipedia
statement (and Meier's formulation "for arbitrary base space $B$", [Lu97, Theorem 1.5]), no
finiteness hypothesis is imposed on $E$ or $B$ here.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Halperin_conjecture)
- [Lu97] G. Lupton, *Variations on a conjecture of Halperin*, Homotopy and Geometry
  (Warsaw, 1997), Banach Center Publ. 45 (1998), 115–135.
  [arXiv:math/0010124](https://arxiv.org/abs/math/0010124)
-/

namespace HalperinConjecture

open CategoryTheory AlgebraicTopology Topology unitInterval
open scoped DirectSum TensorProduct

noncomputable section

/-- The `n`-th rational singular homology group $H_n(X; \mathbb{Q})$ of a topological
space `X`, as a `ℚ`-module. -/
abbrev rationalHomology (X : Type) [TopologicalSpace X] (n : ℕ) : ModuleCat ℚ :=
  ((singularHomologyFunctor (ModuleCat ℚ) n).obj (ModuleCat.of ℚ ℚ)).obj (TopCat.of X)

/-- The map $f_* \colon H_n(X; \mathbb{Q}) \to H_n(Y; \mathbb{Q})$ induced on rational singular
homology by a continuous map `f : X → Y`. -/
abbrev rationalHomologyMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (n : ℕ) : rationalHomology X n ⟶ rationalHomology Y n :=
  ((singularHomologyFunctor (ModuleCat ℚ) n).obj (ModuleCat.of ℚ ℚ)).map (TopCat.ofHom f)

/-- The (rational) *Euler characteristic*
$\chi(X) = \sum_n (-1)^n \dim_{\mathbb{Q}} H_n(X; \mathbb{Q})$ of a topological space `X`.
This is the intended value when the total rational homology of `X` is finite-dimensional
(for instance when `X` is rationally elliptic); otherwise it is a junk value. -/
def eulerCharacteristic (X : Type) [TopologicalSpace X] : ℤ :=
  ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Module.finrank ℚ (rationalHomology X n)

/-- A simply connected topological space `X` is *rationally elliptic* if both its total rational
homology $H_*(X; \mathbb{Q}) = \bigoplus_n H_n(X; \mathbb{Q})$ and its total rational homotopy
$\pi_*(X) \otimes \mathbb{Q} = \bigoplus_{n \ge 2} \pi_n(X, x) \otimes \mathbb{Q}$ are
finite-dimensional. Only the homotopy groups $\pi_n$ with $n \ge 2$ are used since for a simply
connected space $\pi_1$ is trivial and $\pi_0$ is a point; the base point `x` is arbitrary since
`X` is path connected. -/
def IsRationallyElliptic (X : Type) [TopologicalSpace X] : Prop :=
  Module.Finite ℚ (⨁ n, rationalHomology X n) ∧
    ∀ x : X, Module.Finite ℚ (⨁ n, ℚ ⊗[ℤ] Additive (π_ (n + 2) X x))

/-- A continuous map `p : E → B` is a *Serre fibration* if it has the homotopy lifting property
with respect to all cubes $I^n$, $n \ge 0$: for every continuous `f : Iⁿ → E` and every homotopy
`H : I × Iⁿ → B` starting at `p ∘ f`, there is a homotopy `H' : I × Iⁿ → E` starting at `f` that
lifts `H`, i.e. `p ∘ H' = H`. -/
def IsSerreFibration {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) :
    Prop :=
  ∀ (n : ℕ) (f : C(Fin n → I, E)) (H : C(I × (Fin n → I), B)), (∀ y, H (0, y) = p (f y)) →
    ∃ H' : C(I × (Fin n → I), E), (∀ y, H' (0, y) = f y) ∧ ∀ z, p (H' z) = H z

/-- The inclusion $j \colon F = p^{-1}(b) \to E$ of the fibre of `p : E → B` over `b : B`. -/
abbrev fibreInclusion {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (b : B) : C(p ⁻¹' {b}, E) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- A rationally elliptic space has finite-dimensional rational homology in every degree. -/
@[category API, AMS 55]
theorem IsRationallyElliptic.finite_rationalHomology {X : Type} [TopologicalSpace X]
    (hX : IsRationallyElliptic X) (n : ℕ) : Module.Finite ℚ (rationalHomology X n) :=
  have := hX.1
  Module.Finite.of_surjective (DirectSum.component ℚ ℕ (fun n => rationalHomology X n) n)
    fun x => ⟨DirectSum.lof ℚ ℕ _ n x, DirectSum.component.lof_self ..⟩

/-- The Euler characteristic of a point is `1`. -/
@[category test, AMS 55]
theorem eulerCharacteristic_unit : eulerCharacteristic Unit = 1 := by
  have h0 : Module.finrank ℚ (rationalHomology Unit 0) = 1 := by
    have e : rationalHomology Unit 0 ≅ ModuleCat.of ℚ (⨁ _ : Unit, ℚ) :=
      singularHomologyFunctorZeroOfTotallyDisconnectedSpace (ModuleCat ℚ) (ModuleCat.of ℚ ℚ)
        (TopCat.of Unit) ≪≫ ModuleCat.coprodIsoDirectSum _
    rw [e.toLinearEquiv.finrank_eq]
    simp
  have hn (n : ℕ) (hn : n ≠ 0) : Module.finrank ℚ (rationalHomology Unit n) = 0 := by
    have : Subsingleton (rationalHomology Unit n) :=
      ModuleCat.isZero_iff_subsingleton.mp <|
        isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat ℚ) n
          (ModuleCat.of ℚ ℚ) (TopCat.of Unit) hn
    exact Module.finrank_zero_of_subsingleton
  rw [eulerCharacteristic, finsum_eq_single _ 0 fun n hn' => by simp [hn n hn'], h0]
  simp

/-- The identity map is a Serre fibration. -/
@[category API, AMS 55]
theorem isSerreFibration_id (B : Type*) [TopologicalSpace B] :
    IsSerreFibration (ContinuousMap.id B) :=
  fun _ _ H hH => ⟨H, fun y => hH y, fun _ => rfl⟩

/-- The projection of a product onto one of its factors is a Serre fibration. -/
@[category API, AMS 55]
theorem isSerreFibration_fst (B F : Type*) [TopologicalSpace B] [TopologicalSpace F] :
    IsSerreFibration (ContinuousMap.fst : C(B × F, B)) :=
  fun _ f H hH =>
    ⟨H.prodMk (ContinuousMap.snd.comp (f.comp ContinuousMap.snd)),
      fun y => Prod.ext (hH y) rfl, fun _ => rfl⟩

/--
**Halperin conjecture.** Let $F \to E \xrightarrow{p} B$ be a (Serre) fibration of simply
connected spaces, with fibre $F = p^{-1}(b)$. If $F$ is rationally elliptic with Euler
characteristic $\chi(F) \neq 0$, then the rational cohomology Serre spectral sequence of the
fibration collapses at the $E_2$ page. Equivalently, the fibration is TNCZ: the fibre inclusion
$j \colon F \to E$ induces a surjection $H^*(E; \mathbb{Q}) \to H^*(F; \mathbb{Q})$, i.e.
(dually, over the field $\mathbb{Q}$) an injection $j_* \colon H_n(F; \mathbb{Q}) \to
H_n(E; \mathbb{Q})$ in every degree $n$.
-/
@[category research open, AMS 55]
theorem halperin_conjecture {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    [SimplyConnectedSpace E] [SimplyConnectedSpace B]
    (p : C(E, B)) (hp : IsSerreFibration p) (b : B) [SimplyConnectedSpace (p ⁻¹' {b})]
    (hF : IsRationallyElliptic (p ⁻¹' {b})) (hχ : eulerCharacteristic (p ⁻¹' {b}) ≠ 0) (n : ℕ) :
    Function.Injective (rationalHomologyMap (fibreInclusion p b) n).hom := by
  sorry

end

end HalperinConjecture
