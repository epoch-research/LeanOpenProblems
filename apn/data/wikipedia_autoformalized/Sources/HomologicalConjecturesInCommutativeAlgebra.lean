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
# Homological conjectures in commutative algebra

The homological conjectures are a web of interrelated conjectures in commutative algebra.
They relate homological properties of a commutative ring to its internal structure, in
particular to its Krull dimension and depth. This file formalises the list given by
Melvin Hochster, as reproduced on Wikipedia.

Throughout, $A$, $R$ and $S$ are Noetherian commutative rings, $R$ is a local ring with maximal
ideal $\mathfrak m_R$ (except where stated otherwise), and $M$ and $N$ are finitely generated
$R$-modules.

Mathlib does not yet have depth, Cohen–Macaulay rings, regular (local) rings, systems of
parameters or Koszul complexes. This file defines them, in the local Noetherian setting of the
conjectures. The Koszul complex of $x_1, \ldots, x_d$ is built as the exterior algebra
$\bigwedge^\bullet R^d$ with the differential given by contraction against the linear form
$e_i \mapsto x_i$.

*References:*
- [Wikipedia, Homological conjectures in commutative algebra](https://en.wikipedia.org/wiki/Homological_conjectures_in_commutative_algebra)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Ho07] Hochster, M. "Homological conjectures, old and new." _Illinois J. Math._ 51 (2007),
  151–169.
- [An18] André, Y. "La conjecture du facteur direct." _Publ. Math. IHÉS_ 127 (2018), 71–93.
  [arXiv:1609.00345](https://arxiv.org/abs/1609.00345)
-/

open CategoryTheory IsLocalRing RingTheory.Sequence
open scoped TensorProduct

universe u

namespace HomologicalConjecturesInCommutativeAlgebra

/- ### Koszul complexes -/

section Koszul

variable {R : Type u} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Contraction against a linear form lowers the exterior degree by one: it maps
$\bigwedge^{n+1} M$ into $\bigwedge^n M$. -/
@[category API, AMS 13]
lemma contractLeft_mem_exteriorPower (φ : Module.Dual R M) (n : ℕ) :
    ∀ v ∈ ⋀[R]^(n + 1) M, CliffordAlgebra.contractLeft (Q := 0) φ v ∈ ⋀[R]^n M := by
  induction n with
  | zero =>
    intro v hv
    rw [ExteriorAlgebra.exteriorPower, pow_one] at hv
    obtain ⟨m, rfl⟩ := hv
    rw [CliffordAlgebra.contractLeft_ι, ExteriorAlgebra.exteriorPower, pow_zero]
    exact Submodule.algebraMap_mem _
  | succ n ih =>
    intro v hv
    rw [ExteriorAlgebra.exteriorPower, pow_succ'] at hv
    refine Submodule.mul_induction_on hv (fun a ha b hb => ?_) (fun x y hx hy => ?_)
    · obtain ⟨m, rfl⟩ := ha
      rw [CliffordAlgebra.contractLeft_ι_mul]
      refine Submodule.sub_mem _ (Submodule.smul_mem _ _ hb) ?_
      rw [ExteriorAlgebra.exteriorPower, pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ m) (ih b hb)
    · rw [map_add]
      exact Submodule.add_mem _ hx hy

/-- The Koszul differential $\bigwedge^{n+1} M \to \bigwedge^n M$ attached to a linear form
$\varphi$ on $M$: contraction against $\varphi$, so that
$m_0 \wedge \cdots \wedge m_n \mapsto \sum_i (-1)^i \varphi(m_i)\,
m_0 \wedge \cdots \wedge \widehat{m_i} \wedge \cdots \wedge m_n$. -/
noncomputable def koszulD (φ : Module.Dual R M) (n : ℕ) :
    ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  (CliffordAlgebra.contractLeft (Q := 0) φ).restrict (contractLeft_mem_exteriorPower φ n)

/-- The Koszul differential squares to zero. -/
@[category API, AMS 13]
lemma koszulD_comp_koszulD (φ : Module.Dual R M) (n : ℕ) :
    koszulD φ n ∘ₗ koszulD φ (n + 1) = 0 := by
  ext v
  simp [koszulD, LinearMap.restrict_apply, CliffordAlgebra.contractLeft_contractLeft]

/-- In degree one, the Koszul differential $\bigwedge^1 M \to \bigwedge^0 M$ is $\varphi$ itself,
under the canonical identifications $\bigwedge^1 M = M$ and $\bigwedge^0 M = R$. -/
@[category test, AMS 13]
lemma zeroEquiv_koszulD_zero (φ : Module.Dual R M) (v : ⋀[R]^1 M) :
    exteriorPower.zeroEquiv R M (koszulD φ 0 v) = φ (exteriorPower.oneEquiv R M v) := by
  obtain ⟨v, hv⟩ := v
  rw [ExteriorAlgebra.exteriorPower, pow_one] at hv
  obtain ⟨m, rfl⟩ := hv
  have hm : ExteriorAlgebra.ι R m ∈ ⋀[R]^1 M := by
    simp [ExteriorAlgebra.exteriorPower]
  have h1 : (⟨ExteriorAlgebra.ι R m, hm⟩ : ⋀[R]^1 M) =
      exteriorPower.ιMulti R 1 (fun _ => m) := by
    ext
    simp [ExteriorAlgebra.ιMulti_apply]
  have h2 : koszulD φ 0 ⟨ExteriorAlgebra.ι R m, hm⟩ =
      φ m • exteriorPower.ιMulti R 0 (fun i => i.elim0) := by
    ext
    simp [koszulD, LinearMap.restrict_apply, CliffordAlgebra.contractLeft_ι,
      ExteriorAlgebra.ιMulti_zero_apply, Algebra.algebraMap_eq_smul_one]
  rw [h2, map_smul, exteriorPower.zeroEquiv_ιMulti, h1, exteriorPower.oneEquiv_ιMulti]
  simp

/-- The Koszul complex $K_\bullet(x_1, \ldots, x_d; R)$ of the ring $R$ with respect to
$x_1, \ldots, x_d \in R$: the chain complex with $K_n = \bigwedge^n R^d$ (so $K_0 = R$,
$K_d \cong R$ and $K_n = 0$ for $n > d$), and with differential the contraction against the
linear form $R^d \to R$, $e_i \mapsto x_i$. -/
noncomputable def koszulComplex {d : ℕ} (x : Fin d → R) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (⋀[R]^n (Fin d → R)))
    (fun n => ModuleCat.ofHom (koszulD (Fintype.linearCombination R x) n))
    (fun n => by
      rw [← ModuleCat.ofHom_comp, koszulD_comp_koszulD]
      rfl)

@[category API, AMS 13]
lemma koszulComplex_X {d : ℕ} (x : Fin d → R) (n : ℕ) :
    (koszulComplex x).X n = ModuleCat.of R (⋀[R]^n (Fin d → R)) :=
  rfl

@[category API, AMS 13]
lemma koszulComplex_d {d : ℕ} (x : Fin d → R) (n : ℕ) :
    (koszulComplex x).d (n + 1) n =
      ModuleCat.ofHom (koszulD (Fintype.linearCombination R x) n) := by
  simp [koszulComplex]

end Koszul

/- ### Systems of parameters, depth, Cohen–Macaulay and regular rings -/

section Definitions

variable (R : Type*) [CommRing R]

/-- A **regular local ring**: a Noetherian local ring $R$ whose maximal ideal can be generated by
$\dim R$ elements. -/
structure IsRegularLocalRing : Prop extends IsNoetherianRing R, IsLocalRing R where
  exists_finset_span_eq_maximalIdeal :
    ∃ s : Finset R,
      (s.card : WithBot ℕ∞) = ringKrullDim R ∧ Ideal.span (s : Set R) = maximalIdeal R

/-- A **regular ring**: a Noetherian ring all of whose localisations at prime ideals are regular
local rings. -/
structure IsRegularRing : Prop extends IsNoetherianRing R where
  isRegularLocalRing_localization :
    ∀ p : PrimeSpectrum R, IsRegularLocalRing (Localization.AtPrime p.asIdeal)

section LocalRing

variable [IsLocalRing R]

/-- A list $x_1, \ldots, x_n$ of elements of a local ring $R$ is a **system of parameters** if
$n = \dim R$, all $x_i$ lie in the maximal ideal $\mathfrak m_R$, and the ideal
$(x_1, \ldots, x_n)$ is $\mathfrak m_R$-primary, i.e. $\mathfrak m_R \subseteq
\sqrt{(x_1, \ldots, x_n)}$. -/
def IsSystemOfParameters (rs : List R) : Prop :=
  (rs.length : WithBot ℕ∞) = ringKrullDim R ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
    maximalIdeal R ≤ (Ideal.ofList rs).radical

/-- The **depth** of a module $M$ over a local ring $R$: the supremum of the lengths of the
$M$-regular sequences contained in the maximal ideal $\mathfrak m_R$. -/
noncomputable def depth (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  ⨆ (rs : List R) (_ : ∀ r ∈ rs, r ∈ maximalIdeal R) (_ : IsRegular M rs),
    (rs.length : ℕ∞)

/-- A (not necessarily finitely generated) module $W$ over a local ring $R$ is a
**balanced big Cohen–Macaulay module** if $\mathfrak m_R W \neq W$ and every system of
parameters $x_1, \ldots, x_d$ of $R$ is a regular sequence on $W$, i.e. each $x_i$ is a
nonzerodivisor on $W / (x_1, \ldots, x_{i-1}) W$ (as $\mathfrak m_R W \neq W$, this is the same
as `IsRegular`). Applied to an $R$-algebra $B$, this is the notion of a balanced big
Cohen–Macaulay algebra. -/
def IsBalancedBigCohenMacaulay (W : Type*) [AddCommGroup W] [Module R W] : Prop :=
  maximalIdeal R • (⊤ : Submodule R W) ≠ ⊤ ∧
    ∀ rs : List R, IsSystemOfParameters R rs → IsWeaklyRegular W rs

end LocalRing

/-- A **Cohen–Macaulay local ring**: a Noetherian local ring $R$ with
$\operatorname{depth} R = \dim R$. -/
structure IsCohenMacaulayLocalRing : Prop extends IsNoetherianRing R, IsLocalRing R where
  depth_eq : (depth R R : WithBot ℕ∞) = ringKrullDim R

/-- A **Cohen–Macaulay ring**: a Noetherian ring all of whose localisations at maximal ideals are
Cohen–Macaulay local rings. -/
structure IsCohenMacaulayRing : Prop extends IsNoetherianRing R where
  isCohenMacaulayLocalRing_localization :
    ∀ m : MaximalSpectrum R, IsCohenMacaulayLocalRing (Localization.AtPrime m.asIdeal)

end Definitions

section Serre

variable (R : Type u) [CommRing R]

/-- Serre's intersection multiplicity
$$\chi(M, N) = \sum_{i = 0}^{d} (-1)^i \,\ell\bigl(\operatorname{Tor}_i^R(M, N)\bigr)$$
of two finitely generated modules $M$, $N$ over a regular local ring $R$ of dimension $d$. Over
such a ring $\operatorname{Tor}_i^R(M, N) = 0$ for $i > d$, so this is the full alternating sum,
and when $M \otimes_R N$ has finite length so does every $\operatorname{Tor}_i^R(M, N)$, so
that the conversion `ENat.toNat` of the lengths is lossless. -/
noncomputable def serreMultiplicity (d : ℕ) (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : ℤ :=
  ∑ i ∈ Finset.range (d + 1), (-1 : ℤ) ^ i *
    ((Module.length R (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R M)).obj
      (ModuleCat.of R N))).toNat : ℤ)

end Serre

/- ### The conjectures -/

section LocalConjectures

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/--
**The Zero Divisor Theorem.** Let $R$ be a Noetherian local ring and $M \neq 0$ a finitely
generated $R$-module of finite projective dimension. If $r \in R$ is not a zero divisor on $M$,
then $r$ is not a zero divisor on $R$.

Proved by Peskine–Szpiro and Roberts (it follows from the New Intersection Theorem).
-/
@[category research solved, AMS 13]
theorem homological_conjectures_in_commutative_algebra.parts.i
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hM : projectiveDimension (ModuleCat.of R M) ≠ ⊤)
    (r : R) (hr : IsSMulRegular M r) :
    IsSMulRegular R r := by
  sorry

/--
**Bass's Question.** Let $R$ be a Noetherian local ring. If there is a finitely generated
$R$-module $M \neq 0$ of finite injective dimension (i.e. admitting a finite injective
resolution), then $R$ is a Cohen–Macaulay ring.

Answered positively by Peskine–Szpiro and Roberts.
-/
@[category research solved, AMS 13]
theorem homological_conjectures_in_commutative_algebra.parts.ii
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hM : injectiveDimension (ModuleCat.of R M) ≠ ⊤) :
    IsCohenMacaulayLocalRing R := by
  sorry

/--
**The Intersection Theorem.** Let $R$ be a Noetherian local ring and $M$, $N$ finitely generated
$R$-modules such that $M \otimes_R N \neq 0$ has finite length. Then the Krull dimension of $N$,
i.e. $\dim R / \operatorname{Ann}_R N$, is at most the projective dimension of $M$ (the bound
is vacuous if $M$ has infinite projective dimension).

Proved by Peskine–Szpiro and Roberts.
-/
@[category research solved, AMS 13]
theorem homological_conjectures_in_commutative_algebra.parts.iii
    (M N : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hMN : Nontrivial (M ⊗[R] N)) (hMN' : IsFiniteLength R (M ⊗[R] N)) :
    ringKrullDim (R ⧸ Module.annihilator R N) ≤ projectiveDimension (ModuleCat.of R M) := by
  sorry

/--
**The New Intersection Theorem.** Let $R$ be a Noetherian local ring and let
$0 \to G_n \to \cdots \to G_0 \to 0$ be a finite complex of finitely generated free $R$-modules
such that $\bigoplus_i H_i(G_\bullet)$ has finite length but is not $0$. Then $\dim R \leq n$.

Proved by Roberts (1987).
-/
@[category research solved, AMS 13]
theorem homological_conjectures_in_commutative_algebra.parts.iv
    (n : ℕ) (G : ChainComplex (ModuleCat.{u} R) ℕ)
    (hfree : ∀ i, Module.Free R (G.X i)) (hfin : ∀ i, Module.Finite R (G.X i))
    (hn : ∀ i > n, Subsingleton (G.X i))
    (hlen : ∀ i, IsFiniteLength R (G.homology i)) (hne : ∃ i, Nontrivial (G.homology i)) :
    ringKrullDim R ≤ n := by
  sorry

/--
**The Improved New Intersection Conjecture.** Let $R$ be a Noetherian local ring and let
$0 \to G_n \to \cdots \to G_0 \to 0$ be a finite complex of finitely generated free $R$-modules
such that $H_i(G_\bullet)$ has finite length for $i > 0$ and $H_0(G_\bullet)$ has a minimal
generator killed by a power of the maximal ideal $\mathfrak m_R$, i.e. there is
$z \in H_0(G_\bullet) \setminus \mathfrak m_R H_0(G_\bullet)$ with $\mathfrak m_R^k z = 0$ for
some $k$. Then $\dim R \leq n$.

Equivalent to the Canonical Element Conjecture, hence a theorem by André's proof of the
Direct Summand Conjecture.
-/
@[category research solved, AMS 13]
theorem homological_conjectures_in_commutative_algebra.parts.v
    (n : ℕ) (G : ChainComplex (ModuleCat.{u} R) ℕ)
    (hfree : ∀ i, Module.Free R (G.X i)) (hfin : ∀ i, Module.Finite R (G.X i))
    (hn : ∀ i > n, Subsingleton (G.X i))
    (hlen : ∀ i > 0, IsFiniteLength R (G.homology i))
    (hgen : ∃ z : G.homology 0, z ∉ maximalIdeal R • (⊤ : Submodule R (G.homology 0)) ∧
      ∃ k : ℕ, ∀ r ∈ maximalIdeal R ^ k, r • z = 0) :
    ringKrullDim R ≤ n := by
  sorry

end LocalConjectures

/--
**The Direct Summand Conjecture.** Let $R \subseteq S$ be a module-finite ring extension with
$R$ a regular (Noetherian) ring; $R$ need not be local. Then $R$ is a direct summand of $S$ as an
$R$-module, i.e. the inclusion $R \to S$ admits an $R$-linear retraction $S \to R$.

Proved by André using perfectoid spaces [An18].
-/
@[category research solved, AMS 13]
theorem homological_conjectures_in_commutative_algebra.parts.vi
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (hR : IsRegularRing R) (hRS : Function.Injective (algebraMap R S)) :
    ∃ f : S →ₗ[R] R, f ∘ₗ Algebra.linearMap R S = LinearMap.id := by
  sorry

section LocalConjectures

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/--
**The Canonical Element Conjecture.** Let $R$ be a Noetherian local ring of dimension $d$ with
residue field $k$. Let $x_1, \ldots, x_d$ be a system of parameters for $R$, let $F_\bullet$ be a
free $R$-resolution of $k$ with $F_0 = R$, and let $K_\bullet = K_\bullet(x_1, \ldots, x_d; R)$
be the Koszul complex. Lift the identity map $R = K_0 \to F_0 = R$ to a map of complexes
$\alpha \colon K_\bullet \to F_\bullet$. Then, whatever the choice of system of parameters, of
resolution and of lifting, the last map $\alpha_d \colon R = K_d \to F_d$ is not $0$.

Here the identification $F_0 = R$ is an isomorphism `e`, and $K_0 = \bigwedge^0 R^d = R$ is the
canonical isomorphism `exteriorPower.zeroEquiv`; the resolution is a projective resolution all
of whose terms are free.

Equivalent to the Direct Summand Conjecture, hence a theorem by André.
-/
@[category research solved, AMS 13]
theorem homological_conjectures_in_commutative_algebra.parts.vii
    {d : ℕ} (x : Fin d → R) (hx : IsSystemOfParameters R (List.ofFn x))
    (F : ProjectiveResolution (ModuleCat.of R (ResidueField R)))
    (hF : ∀ i, Module.Free R (F.complex.X i))
    (e : F.complex.X 0 ≅ ModuleCat.of R R)
    (α : koszulComplex x ⟶ F.complex)
    (hα : α.f 0 =
      ModuleCat.ofHom (exteriorPower.zeroEquiv R (Fin d → R)).toLinearMap ≫ e.inv) :
    α.f d ≠ 0 := by
  sorry

variable (R) in
/--
**Existence of Balanced Big Cohen–Macaulay Modules Conjecture.** For every Noetherian local ring
$R$ there is a (not necessarily finitely generated) $R$-module $W$ such that
$\mathfrak m_R W \neq W$ and every system of parameters for $R$ is a regular sequence on $W$.

Proved by Hochster–Huneke in equal characteristic and by André in mixed characteristic.
-/
@[category research solved, AMS 13]
theorem homological_conjectures_in_commutative_algebra.parts.viii :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module R W), IsBalancedBigCohenMacaulay R W := by
  sorry

end LocalConjectures

/--
**Cohen–Macaulayness of Direct Summands Conjecture.** Let $R \to S$ be a ring homomorphism of
Noetherian rings with $S$ regular, such that $R$ is a direct summand of $S$ as an $R$-module,
i.e. $R \to S$ admits an $R$-linear retraction. Then $R$ is a Cohen–Macaulay ring.
$R$ need not be local.

Proved by Heitmann–Ma (2018) using weakly functorial big Cohen–Macaulay algebras.
-/
@[category research solved, AMS 13]
theorem homological_conjectures_in_commutative_algebra.parts.ix
    (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing R] [Algebra R S]
    (hS : IsRegularRing S)
    (hRS : ∃ f : S →ₗ[R] R, f ∘ₗ Algebra.linearMap R S = LinearMap.id) :
    IsCohenMacaulayRing R := by
  sorry

/--
**The Vanishing Conjecture for Maps of Tor.** Let $A \subseteq R \to S$ be ring homomorphisms
with $A$ and $S$ regular (Noetherian) rings and $R$ finitely generated as an $A$-module; $R$ need
not be local. Let $W$ be any $A$-module. Then the map
$\operatorname{Tor}_i^A(W, R) \to \operatorname{Tor}_i^A(W, S)$ is zero for all $i \geq 1$.

Known in equal characteristic (Hochster–Huneke), open in mixed characteristic.
-/
@[category research open, AMS 13]
theorem homological_conjectures_in_commutative_algebra.parts.x
    (A R S : Type u) [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] [Algebra R S] [IsScalarTower A R S]
    (hA : IsRegularRing A) (hS : IsRegularRing S)
    (hAR : Function.Injective (algebraMap A R)) [Module.Finite A R]
    (W : Type u) [AddCommGroup W] [Module A W] (i : ℕ) (hi : 1 ≤ i) :
    ((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A W)).map
      (ModuleCat.ofHom (IsScalarTower.toAlgHom A R S).toLinearMap) = 0 := by
  sorry

/--
**The Strong Direct Summand Conjecture.** Let $R \subseteq S$ be a module-finite extension of
complete (Noetherian) local domains, let $x \in R$ be such that $R$ and $R / xR$ are both regular,
and let $Q$ be a height one prime ideal of $S$ lying over $xR$, i.e. $Q \cap R = xR$. Then $xR$
is a direct summand of $Q$ considered as $R$-modules, i.e. $Q = xR \oplus P$ for some
$R$-submodule $P$ of $Q$.

As in the Direct Summand Conjecture that it strengthens, the extension $R \subseteq S$ is
module-finite (this is explicit in Ranganathan's formulation; without it the statement fails).

Equivalent to the Vanishing Conjecture for Maps of Tor; open in general.
-/
@[category research open, AMS 13]
theorem homological_conjectures_in_commutative_algebra.parts.xi
    (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] [IsDomain R] [IsDomain S]
    (hR : IsAdicComplete (maximalIdeal R) R) (hS : IsAdicComplete (maximalIdeal S) S)
    [Algebra R S] [Module.Finite R S] (hRS : Function.Injective (algebraMap R S))
    (x : R) (hreg : IsRegularLocalRing R) (hreg' : IsRegularLocalRing (R ⧸ Ideal.span {x}))
    (Q : Ideal S) [Q.IsPrime] (hQ : Q.primeHeight = 1)
    (hQx : Q.comap (algebraMap R S) = Ideal.span {x}) :
    ∃ P : Submodule R S, Disjoint (Submodule.span R {algebraMap R S x}) P ∧
      Submodule.span R {algebraMap R S x} ⊔ P = Q.restrictScalars R := by
  sorry

/--
**Existence of Weakly Functorial Big Cohen–Macaulay Algebras Conjecture.** Let $R \to S$ be a
local homomorphism of complete (Noetherian) local domains. Then there exist an $R$-algebra $B_R$
that is a balanced big Cohen–Macaulay algebra for $R$, an $S$-algebra $B_S$ that is a balanced
big Cohen–Macaulay algebra for $S$, and a ring homomorphism $B_R \to B_S$ such that the square
$R \to S \to B_S$, $R \to B_R \to B_S$ commutes.

Proved by André (2018), with contributions of Heitmann–Ma and Gabber.
-/
@[category research solved, AMS 13]
theorem homological_conjectures_in_commutative_algebra.parts.xii
    (R S : Type u) [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] [IsDomain R] [IsDomain S]
    (hR : IsAdicComplete (maximalIdeal R) R) (hS : IsAdicComplete (maximalIdeal S) S)
    [Algebra R S] (hRS : IsLocalHom (algebraMap R S)) :
    ∃ (B_R : Type u) (_ : CommRing B_R) (_ : Algebra R B_R)
      (B_S : Type u) (_ : CommRing B_S) (_ : Algebra S B_S),
      IsBalancedBigCohenMacaulay R B_R ∧ IsBalancedBigCohenMacaulay S B_S ∧
      ∃ f : B_R →+* B_S,
        ∀ r : R, f (algebraMap R B_R r) = algebraMap S B_S (algebraMap R S r) := by
  sorry

section LocalConjectures

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/--
**Serre's Conjecture on Multiplicities.** Let $R$ be a regular local ring of dimension $d$ and
$M$, $N$ finitely generated $R$-modules such that $M \otimes_R N$ has finite length. Let
$\chi(M, N) = \sum_i (-1)^i \ell(\operatorname{Tor}_i^R(M, N))$. Then $\chi(M, N) = 0$ if
$\dim M + \dim N < d$, and $\chi(M, N) > 0$ if $\dim M + \dim N = d$, where
$\dim M = \dim R / \operatorname{Ann}_R M$. (Serre proved that $\dim M + \dim N \leq d$ always
holds.)

The vanishing part is a theorem of Roberts and Gillet–Soulé; the positivity part is open in
mixed characteristic.
-/
@[category research open, AMS 13]
theorem homological_conjectures_in_commutative_algebra.parts.xiii
    (hR : IsRegularLocalRing R) (d : ℕ) (hd : ringKrullDim R = d)
    (M N : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hMN : IsFiniteLength R (M ⊗[R] N)) :
    (ringKrullDim (R ⧸ Module.annihilator R M) + ringKrullDim (R ⧸ Module.annihilator R N) < d →
      serreMultiplicity R d M N = 0) ∧
    (ringKrullDim (R ⧸ Module.annihilator R M) + ringKrullDim (R ⧸ Module.annihilator R N) = d →
      0 < serreMultiplicity R d M N) := by
  sorry

/--
**Small Cohen–Macaulay Modules Conjecture.** Let $R$ be a complete Noetherian local ring. Then
there is a finitely generated $R$-module $M \neq 0$ such that some (equivalently, every) system of
parameters for $R$ is a regular sequence on $M$.

Open in dimension at least $3$.
-/
@[category research open, AMS 13]
theorem homological_conjectures_in_commutative_algebra.parts.xiv
    (hR : IsAdicComplete (maximalIdeal R) R) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module R M), Module.Finite R M ∧ Nontrivial M ∧
      ∃ rs : List R, IsSystemOfParameters R rs ∧ IsRegular M rs := by
  sorry

end LocalConjectures

end HomologicalConjecturesInCommutativeAlgebra
