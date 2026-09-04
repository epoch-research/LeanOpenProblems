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
# Resolution of singularities in characteristic $p$

A *resolution of singularities* of an algebraic variety $V$ is a non-singular variety $W$
together with a proper birational morphism $W \to V$. Hironaka (1964) proved that every variety
over a field of characteristic $0$ has a resolution of singularities. Over a field of
characteristic $p > 0$ the existence of a resolution is known in dimension at most $3$
(Abhyankar for curves and surfaces, Cossart–Piltant for threefolds) and is open in general.

Over a non-perfect field "non-singular" is taken to mean *regular*, i.e. all local rings are
regular local rings; this is the notion used in the positive-characteristic results cited below.
Properness of the resolution morphism excludes trivial solutions such as the inclusion of the
regular locus of $V$.

*References:*
- [Wikipedia: Resolution of singularities](https://en.wikipedia.org/wiki/Resolution_of_singularities)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Hir64] H. Hironaka, *Resolution of singularities of an algebraic variety over a field of
  characteristic zero. I, II*, Ann. of Math. 79 (1964).
- [CP08] V. Cossart, O. Piltant, *Resolution of singularities of threefolds in positive
  characteristic. I*, J. Algebra 320 (2008).
- [CP09] V. Cossart, O. Piltant, *Resolution of singularities of threefolds in positive
  characteristic. II*, J. Algebra 321 (2009).
- [Hau10] H. Hauser, *On the problem of resolution of singularities in positive characteristic
  (Or: a proof we are still waiting for)*, Bull. Amer. Math. Soc. 47 (2010).
-/

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace ResolutionOfSingularities

universe u

/-- A local ring `R` is a *regular local ring* if it is Noetherian and its Krull dimension equals
the dimension of its cotangent space $\mathfrak{m} / \mathfrak{m}^2$ over its residue field
$R / \mathfrak{m}$. -/
structure IsRegularLocalRing (R : Type*) [CommRing R] [IsLocalRing R] : Prop where
  isNoetherianRing : IsNoetherianRing R
  ringKrullDim_eq_finrank_cotangentSpace :
    ringKrullDim R = Module.finrank (ResidueField R) (CotangentSpace R)

/-- A scheme `X` is *regular* (or *non-singular*) if the local ring $\mathcal{O}_{X, x}$ at every
point `x` of `X` is a regular local ring. -/
def IsRegular (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

/-- A morphism of schemes `f : W ⟶ V` is *birational* if it restricts to an isomorphism
`f ⁻¹ᵁ U ≅ U` for some dense open `U ⊆ V` whose preimage `f ⁻¹ᵁ U` is dense in `W`.
For integral schemes this says that `f` induces an isomorphism of function fields. -/
def IsBirational {W V : Scheme.{u}} (f : W ⟶ V) : Prop :=
  ∃ U : V.Opens, Dense (X := V) U ∧ Dense (X := W) (f ⁻¹ᵁ U) ∧ IsIso (f ∣_ U)

/-- A scheme `V` over a field `k` is an *(algebraic) variety over `k`* if it is integral,
separated over `k` and of finite type (locally of finite type and quasi-compact) over `k`. -/
structure IsVariety (k : Type u) [Field k] (V : Scheme.{u}) [V.Over (Spec (.of k))] : Prop where
  isIntegral : IsIntegral V
  isSeparated : IsSeparated (V ↘ Spec (.of k))
  locallyOfFiniteType : LocallyOfFiniteType (V ↘ Spec (.of k))
  quasiCompact : QuasiCompact (V ↘ Spec (.of k))

/-- **Resolution of singularities in characteristic $p$.**
Let $k$ be a field of characteristic $p > 0$ and let $V$ be an algebraic variety over $k$
(an integral separated scheme of finite type over $k$). Then there is a regular variety $W$
over $k$ and a proper birational $k$-morphism $W \to V$.

This is known when $\dim V \le 3$ (Abhyankar, Cossart–Piltant) and open when $\dim V \ge 4$. -/
theorem resolution_of_singularities (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (V : Scheme.{u}) [V.Over (Spec (.of k))] (hV : IsVariety k V) :
    ∃ (W : Scheme.{u}) (_ : W.Over (Spec (.of k))) (f : W ⟶ V),
      IsVariety k W ∧ IsRegular W ∧ f.IsOver (Spec (.of k)) ∧ IsProper f ∧
        IsBirational f := by
  sorry

end ResolutionOfSingularities

theorem ResolutionOfSingularities.resolution_of_singularities.disproof : ¬ (type_of% @ResolutionOfSingularities.resolution_of_singularities) := sorry
