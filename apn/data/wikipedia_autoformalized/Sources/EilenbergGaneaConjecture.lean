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
# Eilenberg–Ganea conjecture

The Eilenberg–Ganea conjecture states that if a group $G$ has cohomological dimension $2$, then it
has a $2$-dimensional Eilenberg–MacLane space $K(G, 1)$.

Here the cohomological dimension of $G$ is the integral one,
$$\operatorname{cd}(G) = \sup \{n : H^n(G, M) \neq 0 \text{ for some }
\mathbb{Z}G\text{-module } M\},$$
which is also the projective dimension of the trivial module $\mathbb{Z}$ over the integral group
ring $\mathbb{Z}G$. A $K(G, 1)$ is a path-connected CW complex whose fundamental group is
isomorphic to $G$ and whose higher homotopy groups $\pi_n$, $n \geq 2$, are all trivial.

For $n \neq 2$, a group of cohomological dimension $n$ always has an $n$-dimensional $K(G, 1)$, and
a group of cohomological dimension $2$ always has a $3$-dimensional $K(G, 1)$. Bestvina and Brady
showed that the Eilenberg–Ganea conjecture and the Whitehead asphericity conjecture cannot both be
true.

*References:*
- [Wikipedia, Eilenberg–Ganea conjecture](https://en.wikipedia.org/wiki/Eilenberg%E2%80%93Ganea_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [EG57] Eilenberg, Samuel; Ganea, Tudor. *On the Lusternik–Schnirelmann category of abstract
  groups*. Annals of Mathematics 65 (1957), 517–518. https://doi.org/10.2307/1970062
- [BB97] Bestvina, Mladen; Brady, Noel. *Morse theory and finiteness properties of groups*.
  Inventiones Mathematicae 129 (1997), 445–470. https://doi.org/10.1007/s002220050168
-/

namespace EilenbergGaneaConjecture

open Topology RelCWComplex Set

/-- The (integral) cohomological dimension of a group `G`, as an element of `ℕ∞`: the supremum
of the degrees `n` for which the group cohomology `Hⁿ(G, A)` is nonzero for some `ℤG`-module
`A`, i.e. some `ℤ`-linear representation `A : Rep ℤ G`. It equals the projective dimension of the
trivial `ℤG`-module `ℤ`.

Note that `H⁰(G, ℤ) = ℤ ≠ 0` for the trivial module `ℤ`, so the supremum is never taken over the
empty set. -/
noncomputable def cohomologicalDimension (G : Type) [Group G] : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ∃ A : Rep ℤ G, Nontrivial (groupCohomology A n)), (n : ℕ∞)

/-- The cohomological dimension of `G` is `2` if and only if `H²(G, A) ≠ 0` for some
`ℤG`-module `A` and `Hⁿ(G, A) = 0` for all `n > 2` and all `ℤG`-modules `A`. -/
@[category API, AMS 20]
theorem cohomologicalDimension_eq_two_iff (G : Type) [Group G] :
    cohomologicalDimension G = 2 ↔
      (∃ A : Rep ℤ G, Nontrivial (groupCohomology A 2)) ∧
        ∀ n : ℕ, 2 < n → ∀ A : Rep ℤ G, Subsingleton (groupCohomology A n) := by
  simp only [← not_nontrivial_iff_subsingleton]
  unfold cohomologicalDimension
  set P : ℕ → Prop := fun n => ∃ A : Rep ℤ G, Nontrivial (groupCohomology A n) with hP
  constructor
  · intro h
    have hle : ∀ n, P n → (n : ℕ∞) ≤ 2 := fun n hn =>
      h ▸ le_iSup₂ (f := fun n (_ : P n) => (n : ℕ∞)) n hn
    refine ⟨?_, fun n hn A hA => ?_⟩
    · by_contra h2
      have : ⨆ n, ⨆ (_ : P n), (n : ℕ∞) ≤ 1 := by
        refine iSup₂_le fun n hn => ?_
        have := hle n hn
        have hn2 : n ≠ 2 := fun e => h2 (e ▸ hn)
        norm_cast at this ⊢
        omega
      rw [h] at this
      exact absurd this (by decide)
    · have := hle n ⟨A, hA⟩
      norm_cast at this
      omega
  · rintro ⟨h2, h⟩
    apply le_antisymm
    · refine iSup₂_le fun n hn => ?_
      by_contra hlt
      push_neg at hlt
      obtain ⟨A, hA⟩ := hn
      exact h n (by exact_mod_cast hlt) A hA
    · exact le_iSup₂ (f := fun n (_ : P n) => (n : ℕ∞)) 2 h2

/-- The trivial group has cohomological dimension `0`. -/
@[category test, AMS 20]
theorem cohomologicalDimension_eq_zero_of_subsingleton (G : Type) [Group G] [Subsingleton G] :
    cohomologicalDimension G = 0 := by
  refine le_antisymm (iSup₂_le fun n hn => ?_) (zero_le _)
  obtain ⟨A, hA⟩ := hn
  cases n with
  | zero => exact le_rfl
  | succ n =>
    have := ModuleCat.isZero_iff_subsingleton.1
      (isZero_groupCohomology_succ_of_subsingleton A n)
    exact absurd this (not_subsingleton_iff_nontrivial.2 hA)

/-- A topological space `X` is an Eilenberg–MacLane space `K(G, 1)` for the group `G` if it is
path-connected and, for every basepoint `x`, the fundamental group `π₁(X, x)` is isomorphic to `G`
and the higher homotopy groups `πₙ(X, x)`, `n ≥ 2`, are trivial. The CW complex condition that is
usually part of the definition of a `K(G, 1)` is imposed separately in the conjecture below. -/
def IsEilenbergMacLaneSpace (G : Type*) [Group G] (X : Type*) [TopologicalSpace X] : Prop :=
  PathConnectedSpace X ∧
    ∀ x : X, Nonempty (FundamentalGroup X x ≃* G) ∧ ∀ n : ℕ, 2 ≤ n → Subsingleton (π_ n X x)

/-- The one-point space is a `K(G, 1)` for the trivial group. -/
@[category test, AMS 55]
theorem isEilenbergMacLaneSpace_unit : IsEilenbergMacLaneSpace PUnit Unit := by
  refine ⟨inferInstance, fun _ => ⟨⟨?_⟩, fun n _ => ?_⟩⟩
  · haveI : Subsingleton (FundamentalGroup Unit ()) :=
      inferInstanceAs (Subsingleton (Path.Homotopic.Quotient (() : Unit) ()))
    haveI : Unique (FundamentalGroup Unit ()) := Unique.mk' _
    exact MulEquiv.ofUnique
  · exact Quotient.instSubsingletonQuotient _

/-- **Eilenberg–Ganea conjecture** [EG57]: a group with cohomological dimension $2$ also has a
$2$-dimensional Eilenberg–MacLane space $K(G, 1)$.

That is, if $\operatorname{cd}(G) = 2$, then there is a Hausdorff space $X$ carrying a CW complex
structure of dimension $2$ (no cells of dimension greater than $2$, and at least one $2$-cell) which
is path-connected, has fundamental group isomorphic to $G$, and has trivial homotopy groups
$\pi_n(X)$ for all $n \geq 2$.

Since $\operatorname{cd}(G) = 2$ forces every $K(G, 1)$ to have dimension at least $2$, the
requirement that $X$ has a $2$-cell is automatic; it is included so that $X$ is literally
$2$-dimensional. -/
@[category research open, AMS 20 55 57]
theorem eilenberg_ganea_conjecture (G : Type) [Group G] (hG : cohomologicalDimension G = 2) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      (∀ n : ℕ, 2 < n → IsEmpty (cell (univ : Set X) n)) ∧
        Nonempty (cell (univ : Set X) 2) ∧
        IsEilenbergMacLaneSpace G X := by
  sorry

end EilenbergGaneaConjecture
