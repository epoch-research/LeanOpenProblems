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
# Uniform boundedness conjecture for rational points

Do algebraic curves of genus $g \geq 2$ over number fields $K$ have at most some bounded
number $N(K, g)$ of $K$-rational points?

Following the literature (e.g. [DGH2021]), a curve over $K$ is a smooth, projective,
geometrically irreducible variety of dimension $1$ over $K$. We model it as a scheme `C` with a
structure morphism `f : C ⟶ Spec K` that is proper and smooth of relative dimension `1`, whose
base change to an algebraic closure of `K` is irreducible. The genus of `C` is
$\dim_K H^0(C, \Omega^1_{C/K})$, the dimension of the space of global regular differentials; we
compute it inside the function field $K(C)$ as the space of Kähler differentials of $K(C)/K$
that are regular at every place of $K(C)$ over $K$.

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Uniform_boundedness_conjecture_for_rational_points)
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [CHM1997] L. Caporaso, J. Harris, B. Mazur, *Uniformity of rational points*,
  J. Amer. Math. Soc. 10 (1997), 1–35.
* [DGH2021] V. Dimitrov, Z. Gao, P. Habegger, *Uniformity in Mordell–Lang for curves*,
  Ann. of Math. 194 (2021), 237–298. [arXiv:2001.10276](https://arxiv.org/abs/2001.10276)
-/

namespace UniformBoundednessConjectureForRationalPoints

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

section FunctionField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/--
The `K`-vector space of Kähler differentials of `L` over `K` that are regular at every place of
`L` over `K`.

A `K`-subalgebra `A` of `L` such that `x ∈ A` or `x⁻¹ ∈ A` for every `x : L` is a valuation
subring of `L` containing `K`. When `L = K(C)` is the function field of a smooth projective
curve `C` over `K`, the proper such subalgebras are exactly the local rings `𝒪_{C, P}` at the
closed points `P` of `C` (and `A = L` imposes no condition). A differential `ω ∈ Ω[L⁄K]` is
regular at `P` when it lies in the image of `Ω[𝒪_{C, P}⁄K] → Ω[K(C)⁄K]`. Hence this space is
$H^0(C, \Omega^1_{C/K})$, the space of global sections of the sheaf of differentials.
-/
noncomputable def regularDifferentials : Submodule K Ω[L⁄K] :=
  ⨅ (A : Subalgebra K L) (_ : ∀ x : L, x ∈ A ∨ x⁻¹ ∈ A),
    (LinearMap.range (KaehlerDifferential.map K K A L)).restrictScalars K

/--
The genus of the function field `L` over `K`: the `K`-dimension of the space of differentials
of `L/K` that are regular at every place. For `L = K(C)` the function field of a smooth
projective geometrically irreducible curve `C` over `K` this is
$\dim_K H^0(C, \Omega^1_{C/K})$, the genus of `C`.
-/
noncomputable def functionFieldGenus : ℕ := Module.finrank K (regularDifferentials K L)

end FunctionField

section Curve

variable (K : Type u) [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K))

/--
The set of `K`-rational points of a `K`-scheme `C` with structure morphism `f : C ⟶ Spec K`:
the sections of `f`, that is, the `K`-morphisms `Spec K ⟶ C`.
-/
def rationalPoints : Set (Spec (.of K) ⟶ C) := {s | (s ≫ f) = 𝟙 _}

/--
A `K`-scheme `C` with structure morphism `f : C ⟶ Spec K` is geometrically irreducible if its
base change to an algebraic closure of `K` is irreducible.
-/
def IsGeometricallyIrreducible : Prop :=
  IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))

/--
The genus of an integral `K`-scheme `C` with structure morphism `f : C ⟶ Spec K`, defined as
the genus of its function field `K(C)`, with the `K`-algebra structure on `K(C)` induced by `f`.
When `C` is a smooth projective geometrically irreducible curve over `K`, this is
$\dim_K H^0(C, \Omega^1_{C/K})$, the genus of `C`.
-/
noncomputable def genus [IsIntegral C] : ℕ :=
  haveI : Nonempty (⊤ : C.Opens) := ⟨⟨genericPoint C, trivial⟩⟩
  letI : Algebra K C.functionField :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫ C.germToFunctionField ⊤).hom.toAlgebra
  functionFieldGenus K C.functionField

end Curve

/--
**Uniform boundedness conjecture for rational points.**

Do algebraic curves of genus $g \geq 2$ over number fields $K$ have at most some bounded number
$N(K, g)$ of $K$-rational points?

That is, is it true that for every number field $K$ and every integer $g \geq 2$ there is a
number $N(K, g)$, depending only on $K$ and $g$, such that every smooth projective geometrically
irreducible curve $C$ over $K$ of genus $g$ satisfies $\#C(K) \leq N(K, g)$?

Here a curve is a scheme `C` over `Spec K` that is proper and smooth of relative dimension `1`
(hence projective) and geometrically irreducible. The hypothesis `IsIntegral C` is implied by
these (smooth over a field gives reduced, geometrically irreducible gives irreducible) and is
only needed to speak about the function field of `C`. By Faltings' theorem, each individual
$C(K)$ is finite; the conjecture asks for a bound that is uniform in $C$. The points are counted
with `Set.encard`, so the bound $\#C(K) \leq N$ also asserts that $C(K)$ is finite.
-/
theorem uniform_boundedness_conjecture_for_rational_points :
    ∀ (K : Type u) [Field K] [NumberField K] (g : ℕ), 2 ≤ g →
      ∃ N : ℕ, ∀ (C : Scheme.{u}) (f : C ⟶ Spec (.of K)) [IsIntegral C] [IsProper f]
        [IsSmoothOfRelativeDimension 1 f], IsGeometricallyIrreducible K f → genus K f = g →
        (rationalPoints K f).encard ≤ N := by
  sorry

end UniformBoundednessConjectureForRationalPoints

theorem UniformBoundednessConjectureForRationalPoints.uniform_boundedness_conjecture_for_rational_points.disproof : ¬ (type_of% @UniformBoundednessConjectureForRationalPoints.uniform_boundedness_conjecture_for_rational_points) := sorry
