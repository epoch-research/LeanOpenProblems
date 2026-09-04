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
# Serre's conjecture II

Serre's conjecture II states that if $G$ is a simply connected semisimple algebraic group over a
perfect field $F$ of cohomological dimension at most $2$, then the Galois cohomology set
$H^1(F, G)$ is zero.

Algebraic groups over $F$ are modelled as group objects in the category of schemes over
$\operatorname{Spec} F$. A *linear algebraic group* is a smooth affine group scheme of finite type.
Such a group $G$ is *semisimple* if it is connected and the radical of $G_{\bar F}$ is trivial,
i.e. $G_{\bar F}$ has no nontrivial smooth connected commutative normal subgroup. It is
*simply connected* if every central isogeny $G' \to G$ from a connected linear algebraic group
$G'$ is an isomorphism.

Let $F_s$ be a separable closure of $F$ and $\Gamma_F = \operatorname{Gal}(F_s/F)$ its absolute
Galois group, a profinite group. The field $F$ has *cohomological dimension* at most $n$ if
$H^q(\Gamma_F, A) = 0$ for every discrete torsion $\Gamma_F$-module $A$ and every $q > n$. The
Galois cohomology set $H^1(F, G) = H^1(\Gamma_F, G(F_s))$ is the pointed set of continuous
$1$-cocycles $\Gamma_F \to G(F_s)$ modulo the relation of being cohomologous; it is zero if every
continuous $1$-cocycle is a coboundary. For a perfect field $F$ one has $F_s = \bar F$.

*References:*
- [Wikipedia, Serre's conjecture II](https://en.wikipedia.org/wiki/Serre%27s_conjecture_II_%28algebra%29)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- J.-P. Serre, *Cohomologie galoisienne des groupes algébriques linéaires*, Colloque sur la
  théorie des groupes algébriques, Bruxelles (1962).
- J.-P. Serre, *Cohomologie galoisienne*, Lecture Notes in Mathematics 5, Springer (1994),
  Chapter I §3, Chapter II §2 and Chapter III §3.1.
-/

namespace SerresConjectureII

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Limits
open scoped MonObj GrpObj

universe u

/- ### Cohomological dimension of a field -/

/-- The field $F$ has cohomological dimension at most $n$: for every discrete torsion
$\Gamma_F$-module $A$ (a torsion abelian group with the discrete topology on which the absolute
Galois group $\Gamma_F = \operatorname{Gal}(F_s/F)$, with its Krull topology, acts continuously)
and every $q > n$, the continuous cohomology group $H^q(\Gamma_F, A)$ vanishes.
See Serre, *Cohomologie galoisienne*, Chapter I §3.1 and Chapter II §2. -/
def CohomologicalDimensionLE (F : Type u) [Field F] (n : ℕ) : Prop :=
  ∀ (A : Action (TopModuleCat.{u} ℤ) Gal(SeparableClosure F/F)),
    DiscreteTopology A.V → AddMonoid.IsTorsion A.V →
    Continuous (fun p : Gal(SeparableClosure F/F) × A.V ↦ (A.ρ p.1).hom p.2) →
    ∀ q, n < q → Subsingleton ((continuousCohomology ℤ Gal(SeparableClosure F/F) q).obj A)

/- ### Algebraic groups -/

section AlgebraicGroups

variable {S : Scheme.{u}}

/-- A group scheme `G` over `S` is a *linear algebraic group* if its structure morphism is
affine, of finite type and smooth. -/
class IsLinearAlgebraicGroup (G : Grp (Over S)) : Prop where
  isAffineHom : IsAffineHom G.X.hom
  locallyOfFiniteType : LocallyOfFiniteType G.X.hom
  isSmooth : IsSmooth G.X.hom

/-- A homomorphism of group schemes `f : H ⟶ G` over `S` realises `H` as a *normal closed
subgroup scheme* of `G`: `f` is a closed immersion and, for every `S`-scheme `T`, the subgroup
`H(T)` of `G(T)` is normal. -/
structure IsNormalSubgroupScheme {G H : Grp (Over S)} (f : H ⟶ G) : Prop where
  isClosedImmersion : IsClosedImmersion f.hom.hom.left
  conj_mem : ∀ (T : Over S) (g : T ⟶ G.X) (h : T ⟶ H.X),
    ∃ h' : T ⟶ H.X, (h' ≫ f.hom.hom) = g * (h ≫ f.hom.hom) * g⁻¹

/-- A group scheme `G` over `S` has *trivial radical* if every smooth connected commutative
normal closed subgroup scheme of `G` is trivial, i.e. its structure morphism is an isomorphism.
Over an algebraically closed field this says that the radical of `G` (the largest smooth
connected solvable normal subgroup) is trivial: the last nontrivial term of the derived series of
the radical is a smooth connected commutative normal subgroup. -/
def HasTrivialRadical (G : Grp (Over S)) : Prop :=
  ∀ (H : Grp (Over S)) (f : H ⟶ G), IsNormalSubgroupScheme f →
    IsSmooth H.X.hom → ConnectedSpace H.X.left → IsCommMonObj H.X → IsIso H.X.hom

/-- A homomorphism of group schemes `f : G' ⟶ G` over `S` is a *central isogeny* if it is
surjective, its kernel `G' ×_G S` (the fibre of `f` over the unit section of `G`) is finite over
`S`, and its kernel is central in `G'`: for every `S`-scheme `T`, every element of `G'(T)`
commutes with every element of the kernel of `G'(T) → G(T)`. -/
structure IsCentralIsogeny {G' G : Grp (Over S)} (f : G' ⟶ G) : Prop where
  surjective : Surjective f.hom.hom.left
  isFinite_kernel : IsFinite (pullback.snd f.hom.hom.left η[G.X].left)
  central : ∀ (T : Over S) (g k : T ⟶ G'.X), (k ≫ f.hom.hom) = 1 → g * k = k * g

/-- A group scheme `G` over `S` is *simply connected* if every central isogeny `G' ⟶ G` from a
connected linear algebraic group `G'` is an isomorphism. -/
class IsSimplyConnected (G : Grp (Over S)) : Prop where
  isIso_of_isCentralIsogeny : ∀ (G' : Grp (Over S)) (f : G' ⟶ G), IsLinearAlgebraicGroup G' →
    ConnectedSpace G'.X.left → IsCentralIsogeny f → IsIso f

variable (F : Type u) [Field F]

/-- The base change $G_{\bar F}$ of a group scheme `G` over a field `F` to an algebraic closure
$\bar F$ of `F`. -/
noncomputable def baseChangeAlgebraicClosure (G : Grp (Over (Spec (CommRingCat.of F)))) :
    Grp (Over (Spec (CommRingCat.of (AlgebraicClosure F)))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))))).mapGrp.obj G

variable {F} in
/-- A group scheme `G` over a field `F` is a *semisimple algebraic group* if it is a connected
linear algebraic group (smooth, affine, of finite type) and the radical of $G_{\bar F}$ is
trivial. -/
class IsSemisimple (G : Grp (Over (Spec (CommRingCat.of F)))) : Prop where
  isLinearAlgebraicGroup : IsLinearAlgebraicGroup G
  connectedSpace : ConnectedSpace G.X.left
  hasTrivialRadical : HasTrivialRadical (baseChangeAlgebraicClosure F G)

end AlgebraicGroups

/- ### Galois cohomology -/

section GaloisCohomology

variable (F : Type u) [Field F]

/-- $\operatorname{Spec} F_s$ as a scheme over $\operatorname{Spec} F$, where $F_s$ is a separable
closure of $F$. -/
noncomputable def specSeparableClosure : Over (Spec (CommRingCat.of F)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F (SeparableClosure F))))

/-- The automorphism of $\operatorname{Spec} F_s$ over $\operatorname{Spec} F$ induced by
$\sigma \in \operatorname{Gal}(F_s/F)$. -/
noncomputable def specGal (σ : Gal(SeparableClosure F/F)) :
    specSeparableClosure F ⟶ specSeparableClosure F :=
  Over.homMk (Spec.map (CommRingCat.ofHom (σ : SeparableClosure F →+* SeparableClosure F))) <| by
    simp only [specSeparableClosure, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp

/-- The group $G(F_s)$ of $F_s$-points of a group scheme `G` over `F`. -/
abbrev Points (G : Grp (Over (Spec (CommRingCat.of F)))) : Type u :=
  specSeparableClosure F ⟶ G.X

variable {F}

/-- The natural action of $\operatorname{Gal}(F_s/F)$ on the group $G(F_s)$ by group
automorphisms: $\sigma \in \operatorname{Gal}(F_s/F)$ acts on an $F_s$-point
$x \colon \operatorname{Spec} F_s \to G$ by precomposition with
$\operatorname{Spec}(\sigma)$. -/
noncomputable instance (G : Grp (Over (Spec (CommRingCat.of F)))) :
    MulDistribMulAction Gal(SeparableClosure F/F) (Points F G) where
  smul σ x := specGal F σ ≫ x
  one_smul x := by
    change (specGal F 1 ≫ x) = x
    have : specGal F 1 = 𝟙 _ := by
      apply Over.OverMorphism.ext
      have h : ((1 : Gal(SeparableClosure F/F)) : SeparableClosure F →+* SeparableClosure F) =
          RingHom.id _ := by
        ext
        rfl
      simp [specGal, h]
      rfl
    rw [this, Category.id_comp]
  mul_smul σ τ x := by
    change (specGal F (σ * τ) ≫ x) = (specGal F σ ≫ (specGal F τ ≫ x))
    have : specGal F (σ * τ) = specGal F σ ≫ specGal F τ := by
      apply Over.OverMorphism.ext
      simp only [specGal, Over.homMk_left, Over.comp_left, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      rfl
    rw [this, Category.assoc]
  smul_mul σ x y := by
    change (specGal F σ ≫ (x * y)) = (specGal F σ ≫ x) * (specGal F σ ≫ y)
    rw [Hom.mul_def, Hom.mul_def, comp_lift_assoc]
  smul_one σ := by
    change (specGal F σ ≫ (1 : Points F G)) = 1
    rw [Hom.one_def, comp_toUnit_assoc]

/-- A *continuous $1$-cocycle* of $\operatorname{Gal}(F_s/F)$ with values in $G(F_s)$: a locally
constant map $a$ (i.e. a map continuous for the Krull topology on $\operatorname{Gal}(F_s/F)$ and
the discrete topology on $G(F_s)$) with $a_{\sigma\tau} = a_\sigma \cdot \sigma(a_\tau)$. -/
structure IsCocycle {G : Grp (Over (Spec (CommRingCat.of F)))}
    (a : Gal(SeparableClosure F/F) → Points F G) : Prop where
  isLocallyConstant : IsLocallyConstant a
  cocycle : ∀ σ τ, a (σ * τ) = a σ * σ • a τ

/-- The Galois cohomology set $H^1(F, G) = H^1(\operatorname{Gal}(F_s/F), G(F_s))$ is zero:
every continuous $1$-cocycle is a coboundary, i.e. of the form
$\sigma \mapsto b^{-1} \cdot \sigma(b)$ for some $b \in G(F_s)$. -/
def H1IsTrivial (G : Grp (Over (Spec (CommRingCat.of F)))) : Prop :=
  ∀ a : Gal(SeparableClosure F/F) → Points F G, IsCocycle a →
    ∃ b : Points F G, ∀ σ, a σ = b⁻¹ * σ • b

end GaloisCohomology

/-- **Serre's conjecture II.** If $G$ is a simply connected semisimple algebraic group over a
perfect field $F$ of cohomological dimension at most $2$, then the Galois cohomology set
$H^1(F, G) = H^1(\operatorname{Gal}(\bar F/F), G(\bar F))$ is zero, i.e. every continuous
$1$-cocycle $\operatorname{Gal}(\bar F/F) \to G(\bar F)$ is a coboundary. -/
theorem serres_conjecture_ii (F : Type u) [Field F] [PerfectField F]
    (hF : CohomologicalDimensionLE F 2)
    (G : Grp (Over (Spec (CommRingCat.of F)))) [IsSemisimple G] [IsSimplyConnected G] :
    H1IsTrivial G := by
  sorry

end SerresConjectureII

theorem SerresConjectureII.serres_conjecture_ii.disproof : ¬ (type_of% @SerresConjectureII.serres_conjecture_ii) := sorry
