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
# Zilber–Pink conjecture

Let $X$ be a mixed Shimura variety or a semiabelian variety defined over $\mathbb{C}$, and let
$V \subseteq X$ be a subvariety. Then $V$ contains only finitely many maximal atypical
subvarieties.

Here an *atypical subvariety* of $V$ is an irreducible component $Z$ of an intersection
$V \cap T$, where $T \subseteq X$ is a special subvariety, such that
$\dim Z > \dim V + \dim T - \dim X$.

This file states the semiabelian case (Zilber's conjecture on intersections with tori and its
extension to semiabelian varieties, independently proposed by Bombieri, Masser and Zannier).
The special subvarieties of a semiabelian variety are the translates of irreducible algebraic
subgroups by torsion points.

The mixed Shimura case (Pink's conjecture) is not stated: mixed Shimura varieties and their
special subvarieties are not available in Mathlib.

*References:*
- [Wikipedia, Zilber–Pink conjecture](https://en.wikipedia.org/wiki/Zilber%E2%80%93Pink_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- B. Zilber, *Exponential sums equations and the Schanuel conjecture*, J. London Math. Soc. (2)
  65 (2002), 27–44.
- E. Bombieri, D. Masser, U. Zannier, *Anomalous subvarieties—structure theorems and
  applications*, Int. Math. Res. Not. IMRN 2007, no. 19.
- R. Pink, *A common generalization of the conjectures of André-Oort, Manin-Mumford, and
  Mordell-Lang*, preprint (2005).
-/

namespace ZilberPinkConjecture

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

/-- The base scheme $\operatorname{Spec} \mathbb{C}$. -/
local notation "𝕊" => Spec (CommRingCat.of ℂ)

/- We work with a scheme `X` over $\operatorname{Spec} \mathbb{C}$ that is a group scheme over
$\mathbb{C}$, i.e. a group object in the category of schemes over $\operatorname{Spec} \mathbb{C}$.
The Zariski topology on `X` is the topology of its underlying space, and the dimension of a
subset is its topological Krull dimension. -/

variable (X : Scheme) [X.Over 𝕊] [GrpObj (X.asOver 𝕊)]

/-- The $\mathbb{C}$-points of `X`: the morphisms from the terminal object of the category
of schemes over $\operatorname{Spec} \mathbb{C}$ to `X`, i.e. the sections of the structure
morphism. Since `X` is a group scheme, this is a group (the group $X(\mathbb{C})$). -/
abbrev Points := 𝟙_ (Over 𝕊) ⟶ X.asOver 𝕊

/-- The point of the underlying space of `X` corresponding to a $\mathbb{C}$-point. -/
def Points.toPoint (x : Points X) : X := x.left.base (default : 𝕊)

/-- An *algebraic subgroup* of `X`: a Zariski-closed subset `H` of `X` whose
$\mathbb{C}$-points form a subgroup of $X(\mathbb{C})$. -/
def IsAlgebraicSubgroup (H : Set X) : Prop :=
  IsClosed H ∧ ∃ K : Subgroup (Points X), ∀ x : Points X, x ∈ K ↔ x.toPoint ∈ H

/-- `X` is a *semiabelian variety* over $\mathbb{C}$: a connected commutative algebraic group
over $\mathbb{C}$ (a commutative group scheme of finite type over $\operatorname{Spec} \mathbb{C}$
with irreducible underlying space) that is an extension of an abelian variety by an algebraic
torus.

By Chevalley's structure theorem, a connected commutative algebraic group $X$ over $\mathbb{C}$
has a largest connected affine algebraic subgroup $L \cong \mathbb{G}_m^r \times \mathbb{G}_a^s$,
with $X / L$ an abelian variety; $X$ is semiabelian if and only if $s = 0$, i.e. if and only if
$X$ contains no algebraic subgroup isomorphic to $\mathbb{G}_a$. Since $\mathbb{G}_a(\mathbb{C})$
is torsion-free, while every nontrivial connected algebraic subgroup of a semiabelian variety is
semiabelian and hence has nontrivial torsion, this is equivalent to the condition used here:
every nontrivial irreducible algebraic subgroup of $X$ contains a nontrivial torsion point. -/
structure IsSemiabelianVariety : Prop where
  /-- `X` is locally of finite type over $\mathbb{C}$. -/
  locallyOfFiniteType : LocallyOfFiniteType (X ↘ 𝕊)
  /-- `X` is quasi-compact; together with the previous field, `X` is of finite type over
  $\mathbb{C}$. -/
  compactSpace : CompactSpace X
  /-- `X` is connected (equivalently, irreducible). -/
  irreducibleSpace : IrreducibleSpace X
  /-- The group law of `X` is commutative. -/
  isCommMonObj : IsCommMonObj (X.asOver 𝕊)
  /-- Every nontrivial irreducible algebraic subgroup of `X` contains a nontrivial torsion
  point. -/
  exists_isOfFinOrder : ∀ H : Set X, IsAlgebraicSubgroup X H → IsIrreducible H →
    (∃ x : Points X, x ≠ 1 ∧ x.toPoint ∈ H) →
    ∃ x : Points X, x ≠ 1 ∧ IsOfFinOrder x ∧ x.toPoint ∈ H

/-- Translation $y \mapsto a \cdot y$ by the $\mathbb{C}$-point `a`, as an automorphism of the
$\mathbb{C}$-scheme `X`. -/
noncomputable def translation (a : Points X) : X.asOver 𝕊 ⟶ X.asOver 𝕊 :=
  lift (toUnit _ ≫ a) (𝟙 _) ≫ μ

/-- A *special subvariety* of the semiabelian variety `X`: the translate $a \cdot H$ of an
irreducible algebraic subgroup `H` of `X` by a torsion point `a`. -/
def IsSpecialSubvariety (T : Set X) : Prop :=
  ∃ H : Set X, IsAlgebraicSubgroup X H ∧ IsIrreducible H ∧
    ∃ a : Points X, IsOfFinOrder a ∧ T = (translation X a).left.base '' H

/-- `Z` is an *atypical subvariety* of `V`: an irreducible component of $V \cap T$ for some
special subvariety `T` of `X`, with $\dim Z > \dim V + \dim T - \dim X$, i.e.
$\dim V + \dim T < \dim Z + \dim X$. -/
def IsAtypicalSubvariety (V Z : Set X) : Prop :=
  ∃ T : Set X, IsSpecialSubvariety X T ∧
    Maximal (fun W => IsIrreducible W ∧ W ⊆ V ∩ T) Z ∧
    topologicalKrullDim V + topologicalKrullDim T <
      topologicalKrullDim Z + topologicalKrullDim X

/-- Composing a $\mathbb{C}$-point `y` with the translation by `a` gives the product `a * y`
in the group $X(\mathbb{C})$. -/
@[category API, AMS 14]
theorem comp_translation (a y : Points X) : (y ≫ translation X a : Points X) = a * y := by
  simp only [translation, Hom.mul_def, ← Category.assoc, comp_lift]
  congr 2
  simp

/-- Translation by the identity is the identity. -/
@[category API, AMS 14]
theorem translation_one : translation X 1 = 𝟙 _ := by
  change (toUnit _ ≫ (1 : Points X)) * 𝟙 _ = 𝟙 _
  rw [Hom.one_def, ← Category.assoc, toUnit_unique (toUnit _ ≫ toUnit _) (toUnit _),
    ← Hom.one_def, one_mul]

/-- The whole of `X` is an algebraic subgroup of `X`. -/
@[category test, AMS 14]
theorem isAlgebraicSubgroup_univ : IsAlgebraicSubgroup X Set.univ :=
  ⟨isClosed_univ, ⊤, by simp⟩

/-- An irreducible group scheme `X` over $\mathbb{C}$ is a special subvariety of itself. -/
@[category test, AMS 14]
theorem isSpecialSubvariety_univ [IrreducibleSpace X] : IsSpecialSubvariety X Set.univ :=
  ⟨Set.univ, isAlgebraicSubgroup_univ X, IrreducibleSpace.isIrreducible_univ X, 1,
    IsOfFinOrder.one, by simp [translation_one]⟩

/-- **Zilber–Pink conjecture**, semiabelian case (Zilber; Bombieri–Masser–Zannier).

Let $X$ be a semiabelian variety defined over $\mathbb{C}$ and let $V \subseteq X$ be a
subvariety (an irreducible Zariski-closed subset). Then $V$ contains only finitely many maximal
atypical subvarieties. Here an atypical subvariety of $V$ is an irreducible component $Z$ of
$V \cap T$, where $T \subseteq X$ is a special subvariety (a translate of an irreducible algebraic
subgroup of $X$ by a torsion point), such that $\dim Z > \dim V + \dim T - \dim X$; maximality
is with respect to inclusion among the atypical subvarieties of $V$. -/
@[category research open, AMS 11 14]
theorem zilber_pink_conjecture.parts.ii (hX : IsSemiabelianVariety X) (V : Set X)
    (hV : IsClosed V) (hV' : IsIrreducible V) :
    {Z : Set X | Maximal (IsAtypicalSubvariety X V) Z}.Finite := by
  sorry

end ZilberPinkConjecture
