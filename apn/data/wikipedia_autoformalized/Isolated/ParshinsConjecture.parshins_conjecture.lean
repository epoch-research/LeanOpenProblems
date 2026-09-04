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
# Parshin's conjecture

Parshin's conjecture (also called the Beilinson–Parshin conjecture) states that for every
smooth projective variety $X$ over a finite field, the higher algebraic K-groups of $X$
vanish up to torsion: $K_i(X) \otimes \mathbb{Q} = 0$ for all $i > 0$.

Mathlib has no definition of higher algebraic K-theory, so this file constructs the
algebraic K-groups of a scheme from scratch, following Waldhausen:

* `IsVectorBundle X M` says that the sheaf of $\mathcal{O}_X$-modules `M` is locally free of
  finite rank. The full subcategory of `X.Modules` on these objects, together with the short
  exact sequences of $\mathcal{O}_X$-modules, is the exact category of vector bundles on $X$.
* For an abelian category `A` and a property `P` of objects of `A` (thought of as an exact
  subcategory of `A`), `sConstruction P : SimplexCategoryᵒᵖ ⥤ Cat` is Waldhausen's
  $S_\bullet$-construction: `S_n P` is the category of functors `Ar[n] ⥤ A` sending
  `(i, j)` to an object `F(i, j)` satisfying `P`, with `F(i, i)` zero and with
  `F(i, j) → F(i, k) → F(j, k)` short exact for all `i ≤ j ≤ k`.
* `kSpace P` is the geometric realization $|iS_\bullet P|$ of the bisimplicial set
  $N_\bullet iS_\bullet P$ whose $(n, k)$-simplices are strings of $k$ composable
  isomorphisms in $S_n P$. Waldhausen's K-theory space is the loop space
  $\Omega |iS_\bullet P|$, so that `KGroup P _ i` is $K_i(P) = \pi_{i+1}(|iS_\bullet P|, ∗)$
  with base point the zero object. For an exact category this agrees with Quillen's
  K-theory by Waldhausen's comparison theorem [Wa85, §1.9].
* `algebraicKGroup X i` is the `i`-th algebraic K-group $K_i(X)$ of the scheme `X`, namely
  the `i`-th K-group of the exact category of vector bundles on `X`.

*References:*
* [Wikipedia, Parshin's conjecture](https://en.wikipedia.org/wiki/Parshin%27s_conjecture)
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [Wa85] F. Waldhausen, *Algebraic K-theory of spaces*, Lecture Notes in Math. 1126 (1985),
  318–419.
* [Ka05] B. Kahn, *Algebraic K-theory, algebraic cycles and arithmetic geometry*,
  Handbook of K-theory I, Springer (2005).
-/

open CategoryTheory Limits AlgebraicGeometry Topology ZeroObject
open scoped Simplicial

namespace ParshinsConjecture

universe u v

/- ### Waldhausen's `S_•`-construction -/

section SConstruction

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The object `(i, j)` of the arrow category `Ar[n]` of the poset `[n] = {0 < 1 < ⋯ < n}`,
for `i ≤ j`. -/
abbrev arrowOfLE {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) : Arrow (Fin (n + 1)) :=
  Arrow.mk (homOfLE h)

/-- A functor `F : Ar[n] ⥤ A` is an object of Waldhausen's `S_n P` if all its values `F(i, j)`
satisfy `P`, its values `F(i, i)` on the diagonal are zero objects, and for all `i ≤ j ≤ k` the
sequence `F(i, j) → F(i, k) → F(j, k)` is a short exact sequence in `A`. -/
structure IsSObj (P : ObjectProperty A) {n : ℕ} (F : Arrow (Fin (n + 1)) ⥤ A) : Prop where
  /-- Every value `F(i, j)` satisfies `P`. -/
  prop : ∀ a, P (F.obj a)
  /-- The values `F(i, i)` on the diagonal are zero objects. -/
  isZero : ∀ i : Fin (n + 1), IsZero (F.obj (arrowOfLE (le_refl i)))
  /-- For `i ≤ j ≤ k`, the sequence `F(i, j) → F(i, k) → F(j, k)` is short exact. -/
  shortExact : ∀ (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k),
    ∃ w, (ShortComplex.mk
      (F.map (Arrow.homMk (f := arrowOfLE hij) (g := arrowOfLE (hij.trans hjk))
        (𝟙 i) (homOfLE hjk) (Subsingleton.elim _ _)))
      (F.map (Arrow.homMk (f := arrowOfLE (hij.trans hjk)) (g := arrowOfLE hjk)
        (homOfLE hij) (𝟙 k) (Subsingleton.elim _ _))) w).ShortExact

variable (P : ObjectProperty A)

/-- The objects of `S_n P`, as a property of functors `Ar[n] ⥤ A`. -/
def sProp (n : SimplexCategory) : ObjectProperty (Arrow (Fin (n.len + 1)) ⥤ A) :=
  fun F => IsSObj P F

/-- The property `IsSObj P` is stable under precomposition with the functor `Ar[m] ⥤ Ar[n]`
induced by a monotone map `θ : [m] → [n]`; this gives the simplicial structure of `S_• P`. -/
lemma IsSObj.comp {m n : SimplexCategory} (θ : m ⟶ n) {F : Arrow (Fin (n.len + 1)) ⥤ A}
    (hF : IsSObj P F) : IsSObj P (θ.toOrderHom.monotone.functor.mapArrow ⋙ F) where
  prop _ := hF.prop _
  isZero i := hF.isZero (θ.toOrderHom i)
  shortExact _ _ _ hij hjk :=
    hF.shortExact _ _ _ (θ.toOrderHom.monotone hij) (θ.toOrderHom.monotone hjk)

/-- Waldhausen's `S_•`-construction of `P`, as a simplicial category: `S_n P` is the full
subcategory of `Ar[n] ⥤ A` on the objects satisfying `IsSObj P`, and a monotone map
`θ : [m] → [n]` acts by precomposition with the induced functor `Ar[m] ⥤ Ar[n]`. -/
def sConstruction : SimplexCategoryᵒᵖ ⥤ Cat where
  obj n := Cat.of (sProp P n.unop).FullSubcategory
  map θ := Functor.toCatHom <| (sProp P _).lift ((sProp P _).ι ⋙
    (Functor.whiskeringLeft _ _ A).obj θ.unop.toOrderHom.monotone.functor.mapArrow)
    (fun F => F.2.comp P θ.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

end SConstruction

/- ### The K-theory space and the K-groups -/

/-- The core (the groupoid of isomorphisms) of a category, as a functor `Cat ⥤ Cat`. -/
def coreFunctor : Cat.{v, u} ⥤ Cat.{v, u} where
  obj C := Cat.of (Core C)
  map F := F.toFunctor.core.toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The diagonal simplicial set of a bisimplicial set. -/
def diagonal (B : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : SSet.{u} :=
  Functor.diag _ ⋙ Functor.uncurry.obj B

section KTheory

variable {A : Type u} [Category.{v} A] [Abelian A] (P : ObjectProperty A)

/-- The diagonal of the bisimplicial set `N_• iS_• P`, whose `(n, k)`-simplices are strings of
`k` composable isomorphisms in `S_n P`. -/
def kSimplicialSet : SSet := diagonal (sConstruction P ⋙ coreFunctor ⋙ nerveFunctor)

/-- The geometric realization `|iS_• P|`. Waldhausen's K-theory space of `P` is the loop space
of this space. -/
noncomputable def kSpace : TopCat := SSet.toTop.obj (kSimplicialSet P)

/-- The object of `S_0 P` given by the constant functor at the zero object. -/
noncomputable def zeroSObj (hP : P 0) : (sProp P ⦋0⦌).FullSubcategory where
  obj := (Functor.const _).obj 0
  property :=
    { prop := fun _ => hP
      isZero := fun _ => isZero_zero A
      shortExact := fun _ _ _ _ _ => ⟨(isZero_zero A).eq_of_src _ _,
        { exact := ShortComplex.exact_of_isZero_X₂ _ (isZero_zero A)
          mono_f := by dsimp; infer_instance
          epi_g := by dsimp; infer_instance }⟩ }

/-- The base point of `kSpace P`: the vertex given by the zero object. -/
noncomputable def kBasepoint (hP : P 0) : kSpace P :=
  TopCat.toSSetObjEquiv _ _
    ((sSetTopAdj.unit.app (kSimplicialSet P)).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ (Core.mk (zeroSObj P hP))))
    ⟨_, ite_eq_mem_stdSimplex ℝ (0 : Fin 1)⟩

/-- The `i`-th K-group `K_i P = π_{i+1}(|iS_• P|, ∗)` of `P`, where `∗` is the vertex given by
the zero object. -/
noncomputable abbrev KGroup (hP : P 0) (i : ℕ) : Type _ :=
  π_ (i + 1) (kSpace P) (kBasepoint P hP)

end KTheory

/- ### Vector bundles and the algebraic K-theory of a scheme -/

section VectorBundles

variable (X : Scheme.{u})

/-- A sheaf of `𝒪_X`-modules `M` is a vector bundle (i.e. locally free of finite rank) if
every point has an open neighbourhood `U` such that the restriction of `M` to `U` is
isomorphic to a free `𝒪_U`-module of some finite rank `n`. -/
def IsVectorBundle (M : X.Modules) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (n : ℕ), x ∈ U ∧
    Nonempty (M.restrict U.ι ≅
      SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf) (ULift.{u} (Fin n)))

/-- The zero sheaf is a vector bundle (of rank `0`). -/
theorem isVectorBundle_zero : IsVectorBundle X 0 :=
  fun _ => ⟨⊤, 0, trivial, ⟨IsZero.iso
    ((Scheme.Modules.restrictFunctor _).map_isZero (isZero_zero _))
    ((isColimitEquivIsInitialOfIsEmpty _ (colimit.cocone _) (colimit.isColimit _)).isZero)⟩⟩

/-- The `i`-th algebraic K-group `K_i(X)` of a scheme `X`, defined as the `i`-th K-group of the
exact category of vector bundles on `X` (with base point the zero vector bundle). -/
noncomputable abbrev algebraicKGroup (i : ℕ) : Type _ :=
  KGroup (IsVectorBundle X) (isVectorBundle_zero X) i

end VectorBundles

/-- A morphism of schemes `f : X ⟶ S` is projective if it factors as a closed immersion
`X ⟶ ℙ^n_S` followed by the projection `ℙ^n_S ⟶ S`, for some `n`. -/
def IsProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (n : ℕ) (g : X ⟶ ℙ(Fin (n + 1); S)),
    IsClosedImmersion g ∧ CategoryStruct.comp g (pullback.fst _ _) = f

/-- The higher K-groups `K_i(X)`, `i ≥ 1`, are abelian groups. -/
noncomputable example (X : Scheme.{u}) (i : ℕ) : CommGroup (algebraicKGroup X (i + 1)) :=
  inferInstance

/--
**Parshin's conjecture.** Let $X$ be a smooth projective variety over a finite field $k$.
Then the higher algebraic K-groups of $X$ vanish up to torsion: for every $i > 0$,
$K_i(X) \otimes \mathbb{Q} = 0$, i.e. every element of $K_i(X)$ has finite order.

Here a variety over $k$ is an integral scheme `X` with a morphism `f : X ⟶ Spec k`; it is
smooth (resp. projective) if `f` is. Since `K_i(X)` is an abelian group, `Monoid.IsTorsion`
is equivalent to $K_i(X) \otimes \mathbb{Q} = 0$.
-/
theorem parshins_conjecture (k : Type u) [Field k] [Finite k] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsSmooth f] (hf : IsProjective f) (i : ℕ) (hi : 0 < i) :
    Monoid.IsTorsion (algebraicKGroup X i) := by
  sorry

end ParshinsConjecture

theorem ParshinsConjecture.parshins_conjecture.disproof : ¬ (type_of% @ParshinsConjecture.parshins_conjecture) := sorry
