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
# Section conjecture

Grothendieck's section conjecture. Let $k$ be a field finitely generated over $\mathbb{Q}$,
let $X$ be a complete (i.e. proper) smooth geometrically connected curve of genus at least $2$
over $k$, and let $\bar{x}$ be a geometric point of $X$. The structure map $X \to \mathrm{Spec}(k)$
induces a homomorphism of profinite groups
$$p \colon \pi_1(X, \bar{x}) \to \mathrm{Gal}(\bar{k}/k)$$
from the étale fundamental group of $X$ to the absolute Galois group of $k$.
Every rational point $x \in X(k)$ induces a continuous section of $p$ (its decomposition group),
well defined up to conjugation by the geometric fundamental group
$\pi_1(X_{\bar{k}}, \bar{x}) = \ker p$. The conjecture says that the resulting map
$$X(k) \to \{\text{continuous sections of } p\} / \pi_1(X_{\bar{k}}, \bar{x})\text{-conjugacy}$$
is a bijection.

Mathlib does not have the étale fundamental group of a scheme or the genus of a curve, so this
file defines them from scratch:

* `FiniteEtale X` is the category of finite étale schemes over `X`,
  `fiberFunctor xbar : FiniteEtale X ⥤ Type u` is the fiber functor of a geometric point
  `xbar : Spec Ω ⟶ X`, and `etaleFundamentalGroup xbar` is its automorphism group, with the
  profinite topology (the coarsest topology for which the action on each fiber is continuous).
* For a scheme `X` over `k` with a geometric point `xbar` over the canonical geometric point
  `ȷ̄ : Spec k̄ ⟶ Spec k`, the map `p : π₁(X, xbar) → Gal(k̄/k)` is encoded by the
  relation `LiesOver f η σ`: it holds when `η` acts on the fiber of every cover pulled back
  from `Spec k` in the same way as `σ ∈ Gal(k̄/k)`. In particular, `η ∈ ker p` if and only if
  `LiesOver f η 1`.
* `rationalPointSection x : Gal(k̄/k) →* π₁(X, x ∘ ȷ̄)` is the section induced by a rational
  point `x` at the tautological geometric point `x ∘ ȷ̄`, and `IsInducedBy f xbar s x` says
  that `s` is the conjugate of `rationalPointSection x` by some path (isomorphism of fiber
  functors) from `x ∘ ȷ̄` to `xbar` lying over `k`. Such paths form a torsor under
  `ker p = π₁(X_k̄, xbar)`, so the homomorphisms `s` satisfying `IsInducedBy f xbar s x` form
  exactly the `π₁(X_k̄, xbar)`-conjugacy class of the section induced by `x`.
* `genus f` is the dimension over `k` of the space of global sections of the sheaf of relative
  differentials `Ω¹_{X/k}`, realised as compatible families of Kähler differentials on the
  affine opens of `X`.

*References:*
* [Wikipedia, Section conjecture](https://en.wikipedia.org/wiki/Section_conjecture)
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* A. Grothendieck, *Brief an G. Faltings* (letter to G. Faltings, 27 June 1983), in
  *Geometric Galois actions, 1*, London Math. Soc. Lecture Note Ser. 242, Cambridge Univ. Press,
  1997, pp. 49–58.
* J. Stix, *Rational points and arithmetic of fundamental groups: evidence for the section
  conjecture*, Lecture Notes in Mathematics 2054, Springer, 2013.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace SectionConjecture

universe u

section EtaleFundamentalGroup

/-- The category of finite étale schemes over `X`. -/
abbrev FiniteEtale (X : Scheme.{u}) : Type _ :=
  MorphismProperty.Over (@IsFinite ⊓ @IsEtale) ⊤ X

variable {X : Scheme.{u}} {Ω : CommRingCat.{u}} (xbar : Spec Ω ⟶ X)

/-- The fiber functor of a geometric point `xbar : Spec Ω ⟶ X` (the intended use is `Ω` an
algebraically closed field): it sends a finite étale `Y ⟶ X` to the set of lifts of `xbar`
to `Y`. -/
def fiberFunctor : FiniteEtale X ⥤ Type u where
  obj Y := { y : Spec Ω ⟶ Y.left // (y ≫ Y.hom) = xbar }
  map {Y Z} g y := ⟨y.1 ≫ g.left, by rw [Category.assoc, MorphismProperty.Over.w, y.2]⟩

/-- The étale fundamental group `π₁(X, xbar)` of `X` at the geometric point `xbar`: the
automorphism group of the fiber functor. -/
abbrev etaleFundamentalGroup := Aut (fiberFunctor xbar)

/-- The profinite topology on `π₁(X, xbar)`: the topology induced by the embedding into the
product, over all finite étale `Y ⟶ X`, of the sets of self-maps of the (finite) fibers
`(fiberFunctor xbar).obj Y`, each fiber carrying the discrete topology. -/
instance : TopologicalSpace (etaleFundamentalGroup xbar) :=
  TopologicalSpace.induced
    (fun (α : etaleFundamentalGroup xbar) (Y : FiniteEtale X) (y : (fiberFunctor xbar).obj Y) =>
      α.hom.app Y y)
    (Pi.topologicalSpace (t₂ := fun _ => Pi.topologicalSpace (t₂ := fun _ => ⊥)))

end EtaleFundamentalGroup

section GaloisGroup

variable {k : Type u} [Field k]

/-- The canonical geometric point `ȷ̄ : Spec k̄ ⟶ Spec k` of `Spec k`, where `k̄` is the
algebraic closure of `k`. -/
noncomputable def specAlgebraicClosure (k : Type u) [Field k] :
    Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))

/-- The automorphism of `Spec k̄` induced by an element `σ` of the absolute Galois group
`Gal(k̄/k)` of `k`. Precomposition with `galSpec σ` is a left action of `Gal(k̄/k)` on morphisms
`Spec k̄ ⟶ Y`. -/
noncomputable def galSpec (σ : Field.absoluteGaloisGroup k) :
    Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of (AlgebraicClosure k)) :=
  Spec.map (CommRingCat.ofHom
    (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ).toRingEquiv.toRingHom)

/-- `galSpec σ` is an automorphism of `Spec k̄` over `Spec k`. -/
@[category API, AMS 14]
theorem galSpec_comp_specAlgebraicClosure (σ : Field.absoluteGaloisGroup k) :
    (galSpec σ ≫ specAlgebraicClosure k) = specAlgebraicClosure k := by
  simp only [galSpec, specAlgebraicClosure, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ).commutes x

/-- `galSpec` is compatible with multiplication: precomposition with `galSpec` is a left action. -/
@[category API, AMS 14]
theorem galSpec_mul (σ τ : Field.absoluteGaloisGroup k) :
    galSpec (σ * τ) = galSpec σ ≫ galSpec τ := by
  simp only [galSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- `galSpec 1` is the identity. -/
@[category API, AMS 14]
theorem galSpec_one : galSpec (1 : Field.absoluteGaloisGroup k) = 𝟙 _ := by
  simp only [galSpec]
  rw [← Spec.map_id]
  rfl

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Let `xbar, xbar' : Spec k̄ ⟶ X` be geometric points of `X` lying over
`ȷ̄ : Spec k̄ ⟶ Spec k`, and let `η : fiberFunctor xbar' ⟶ fiberFunctor xbar`. Then `η`
*lies over* `σ ∈ Gal(k̄/k)` if, for every finite étale `Z ⟶ X` which is the pullback along `f`
of a finite étale `g : Y ⟶ Spec k` (via `p : Z ⟶ Y`), the map induced by `η` on the fiber
`{y : Spec k̄ ⟶ Y // y ≫ g = ȷ̄}` of `Y` at `ȷ̄` is the action of `σ` (precomposition with
`galSpec σ`).

For `η = α.hom` with `α ∈ π₁(X, xbar)`, this says that the image of `α` under the map
`π₁(X, xbar) → π₁(Spec k, ȷ̄) = Gal(k̄/k)` induced by `f` is `σ`. -/
def LiesOver {xbar xbar' : Spec (.of (AlgebraicClosure k)) ⟶ X}
    (η : fiberFunctor xbar' ⟶ fiberFunctor xbar) (σ : Field.absoluteGaloisGroup k) : Prop :=
  ∀ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of k)) [IsFinite g] [IsEtale g] (Z : FiniteEtale X)
    (p : Z.left ⟶ Y), IsPullback p Z.hom g f →
    ∀ z : (fiberFunctor xbar').obj Z, ((η.app Z z).1 ≫ p) = galSpec σ ≫ z.1 ≫ p

/-- The identity lies over `1`. -/
@[category API, AMS 14]
theorem liesOver_id (xbar : Spec (.of (AlgebraicClosure k)) ⟶ X) :
    LiesOver f (𝟙 (fiberFunctor xbar)) 1 := by
  intro Y g _ _ Z p _ z
  simp [galSpec_one]

/-- If `η` lies over `σ` and `η'` lies over `τ`, then `η ≫ η'` lies over `τ * σ`. -/
@[category API, AMS 14]
theorem liesOver_comp {xbar xbar' xbar'' : Spec (.of (AlgebraicClosure k)) ⟶ X}
    {η : fiberFunctor xbar'' ⟶ fiberFunctor xbar'}
    {η' : fiberFunctor xbar' ⟶ fiberFunctor xbar}
    {σ τ : Field.absoluteGaloisGroup k} (hη : LiesOver f η σ) (hη' : LiesOver f η' τ) :
    LiesOver f (η ≫ η') (τ * σ) := by
  intro Y g _ _ Z p hp z
  rw [NatTrans.comp_app, types_comp_apply, hη' Y g Z p hp, hη Y g Z p hp, galSpec_mul,
    Category.assoc]

/-- The `k`-rational points of `X`, i.e. the sections of `f : X ⟶ Spec k`. -/
def RationalPoint : Type u := { x : Spec (.of k) ⟶ X // (x ≫ f) = 𝟙 _ }

/-- The section `Gal(k̄/k) → π₁(X, x ∘ ȷ̄)` induced by a `k`-point `x : Spec k ⟶ X` of `X`,
at the tautological geometric point `x ∘ ȷ̄` (where `ȷ̄ : Spec k̄ ⟶ Spec k`): an element
`σ` acts on lifts `Spec k̄ ⟶ Y` of `x ∘ ȷ̄` by precomposition with `galSpec σ`. -/
noncomputable def rationalPointSection (x : Spec (.of k) ⟶ X) :
    Field.absoluteGaloisGroup k →* etaleFundamentalGroup (specAlgebraicClosure k ≫ x) where
  toFun σ := NatIso.ofComponents (fun Z => Equiv.toIso
    { toFun := fun z => ⟨galSpec σ ≫ z.1, by
        rw [Category.assoc, z.2, ← Category.assoc, galSpec_comp_specAlgebraicClosure]⟩
      invFun := fun z => ⟨galSpec σ⁻¹ ≫ z.1, by
        rw [Category.assoc, z.2, ← Category.assoc, galSpec_comp_specAlgebraicClosure]⟩
      left_inv := fun z => Subtype.ext <| by
        simp only [← Category.assoc, ← galSpec_mul, inv_mul_cancel, galSpec_one,
          Category.id_comp]
      right_inv := fun z => Subtype.ext <| by
        simp only [← Category.assoc, ← galSpec_mul, mul_inv_cancel, galSpec_one,
          Category.id_comp] })
    (fun {Z Z'} h => by
      ext z
      simp [fiberFunctor])
  map_one' := Aut.ext <| NatTrans.ext <| funext fun Z => funext fun z => Subtype.ext <| by
    simp [galSpec_one]
    rfl
  map_mul' σ τ := Aut.ext <| NatTrans.ext <| funext fun Z => funext fun z => Subtype.ext <| by
    simp [galSpec_mul, Aut.Aut_mul_def]

/-- The homomorphism induced by a rational point is a section: `rationalPointSection x σ`
lies over `σ`. -/
@[category API, AMS 14]
theorem liesOver_rationalPointSection (x : Spec (.of k) ⟶ X) (σ : Field.absoluteGaloisGroup k) :
    LiesOver f (rationalPointSection x σ).hom σ := by
  intro Y g _ _ Z p _ z
  simp [rationalPointSection]

/-- A homomorphism `s : Gal(k̄/k) →* π₁(X, xbar)` *is induced by* the `k`-point
`x : Spec k ⟶ X` if `s` is obtained from the section
`rationalPointSection x : Gal(k̄/k) →* π₁(X, x ∘ ȷ̄)` by transport of structure along a path
`γ : fiberFunctor (x ∘ ȷ̄) ≅ fiberFunctor xbar` lying over `k` (that is, inducing the identity
on the fibers of covers pulled back from `Spec k`).

Such paths form a torsor under `ker(π₁(X, xbar) → Gal(k̄/k)) = π₁(X_k̄, xbar)`, so the
homomorphisms induced by `x` form exactly the `π₁(X_k̄, xbar)`-conjugacy class of sections
attached to `x`. -/
def IsInducedBy (xbar : Spec (.of (AlgebraicClosure k)) ⟶ X)
    (s : Field.absoluteGaloisGroup k →* etaleFundamentalGroup xbar)
    (x : Spec (.of k) ⟶ X) : Prop :=
  ∃ γ : fiberFunctor (specAlgebraicClosure k ≫ x) ≅ fiberFunctor xbar,
    LiesOver f γ.hom 1 ∧ ∀ σ, s σ = γ.symm ≪≫ rationalPointSection x σ ≪≫ γ

/-- The tautological section attached to a rational point `x` is induced by `x`. -/
@[category API, AMS 14]
theorem isInducedBy_rationalPointSection (x : Spec (.of k) ⟶ X) :
    IsInducedBy f (specAlgebraicClosure k ≫ x) (rationalPointSection x) x :=
  ⟨Iso.refl _, liesOver_id f _, fun σ => by simp⟩

end GaloisGroup

section Genus

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The ring of sections `Γ(X, U)`, regarded as a `k`-algebra via `f : X ⟶ Spec k`. -/
def Sections (_f : X ⟶ Spec (.of k)) (U : X.Opens) : Type u := Γ(X, U)

variable (f : X ⟶ Spec (.of k))

instance (U : X.Opens) : CommRing (Sections f U) := inferInstanceAs (CommRing Γ(X, U))

/-- The structure map `k → Γ(X, U)` induced by `f`. -/
noncomputable def toSections (U : X.Opens) : k →+* Sections f U :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom

noncomputable instance (U : X.Opens) : Algebra k (Sections f U) := (toSections f U).toAlgebra

/-- The restriction map `Γ(X, U) → Γ(X, V)` for `V ≤ U`. -/
def restriction {U V : X.Opens} (h : V ≤ U) : Sections f U →+* Sections f V :=
  (X.presheaf.map (homOfLE h).op).hom

/-- The restriction maps are `k`-algebra homomorphisms. -/
@[category API, AMS 14]
theorem restriction_comp_toSections {U V : X.Opens} (h : V ≤ U) :
    (restriction f h).comp (toSections f U) = toSections f V := by
  simp only [restriction, toSections]
  rw [← CommRingCat.hom_comp, Category.assoc, Category.assoc, ← Functor.map_comp]
  rfl

/-- For `V ≤ U`, `Γ(X, V)` is a `Γ(X, U)`-algebra compatibly with the `k`-algebra structures. -/
@[category API, AMS 14]
theorem isScalarTower {U V : X.Opens} (h : V ≤ U) :
    letI := (restriction f h).toAlgebra
    IsScalarTower k (Sections f U) (Sections f V) := by
  letI := (restriction f h).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun c =>
    (RingHom.congr_fun (restriction_comp_toSections f h) c).symm

/-- The `k`-vector space `H⁰(X, Ω¹_{X/k})` of global sections of the sheaf of relative
differentials of `X` over `k`: families of Kähler differentials `ω U ∈ Ω[Γ(X, U)⁄k]`,
indexed by the affine opens `U` of `X`, compatible with restriction. (Since the affine opens
form a basis of the topology of `X` and `Ω¹_{X/k}` restricted to an affine open `U` is the
quasi-coherent sheaf associated to `Ω[Γ(X, U)⁄k]`, this is the space of global sections of
`Ω¹_{X/k}`.) -/
noncomputable def globalDifferentials :
    Submodule k (∀ U : X.affineOpens, Ω[Sections f U.1⁄k]) where
  carrier := { ω | ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1),
    letI := (restriction f h).toAlgebra
    haveI := isScalarTower f h
    KaehlerDifferential.map k k (Sections f U.1) (Sections f V.1) (ω U) = ω V }
  zero_mem' := by
    intro U V h
    simp
  add_mem' := by
    intro ω ω' hω hω' U V h
    simp only [Pi.add_apply, map_add]
    rw [hω U V h, hω' U V h]
  smul_mem' := by
    intro c ω hω U V h
    letI := (restriction f h).toAlgebra
    haveI := isScalarTower f h
    simp only [Pi.smul_apply]
    rw [← hω U V h, LinearMap.map_smul_of_tower]

/-- The genus of a smooth proper geometrically connected curve `X` over `k`:
the dimension over `k` of `H⁰(X, Ω¹_{X/k})`. -/
noncomputable def genus : ℕ := Module.finrank k (globalDifferentials f)

end Genus

/-- **Section conjecture** (Grothendieck, 1983).

Let $k$ be a field finitely generated over $\mathbb{Q}$ and let $X$ be a complete (proper) smooth
geometrically connected curve of genus at least $2$ over $k$. Fix a geometric point
$\bar{x} \colon \mathrm{Spec}(\bar{k}) \to X$ lying over
$\bar{\jmath} \colon \mathrm{Spec}(\bar{k}) \to \mathrm{Spec}(k)$. Then every continuous section
$s$ of the homomorphism $\pi_1(X, \bar{x}) \to \mathrm{Gal}(\bar{k}/k)$ induced by the structure
map $X \to \mathrm{Spec}(k)$ is induced by a unique rational point $x \in X(k)$, i.e. $s$ is
$\pi_1(X_{\bar{k}}, \bar{x})$-conjugate to the section attached to $x$ for exactly one
$x \in X(k)$. Equivalently, the map from $X(k)$ to the set of continuous sections modulo
conjugation by the geometric fundamental group $\pi_1(X_{\bar{k}}, \bar{x})$ is a bijection. -/
@[category research open, AMS 11 14]
theorem section_conjecture {k : Type u} [Field k] [CharZero k]
    (hk : (⊤ : IntermediateField ℚ k).FG)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsSmoothOfRelativeDimension 1 f]
    [ConnectedSpace (pullback f (specAlgebraicClosure k) : Scheme.{u})] (hg : 2 ≤ genus f)
    (xbar : Spec (.of (AlgebraicClosure k)) ⟶ X) (hxbar : (xbar ≫ f) = specAlgebraicClosure k)
    (s : Field.absoluteGaloisGroup k →* etaleFundamentalGroup xbar) (hs : Continuous s)
    (hsec : ∀ σ, LiesOver f (s σ).hom σ) :
    ∃! x : RationalPoint f, IsInducedBy f xbar s x.1 := by
  sorry

end SectionConjecture
