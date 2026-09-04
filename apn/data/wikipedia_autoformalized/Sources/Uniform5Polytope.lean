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
# Convex uniform 5-polytopes

A *convex uniform polytope* is defined recursively on the dimension. A uniform $0$-polytope is a
point. A uniform $d$-polytope ($d \ge 1$) is a convex $d$-polytope that is vertex-transitive (the
isometries of the ambient space mapping it onto itself act transitively on its vertices), whose
edges all have the same length, and whose facets are uniform $(d-1)$-polytopes. In dimension $2$
this gives the regular polygons and in dimension $3$ the convex uniform polyhedra (Platonic and
Archimedean solids, prisms and antiprisms). For $d \ge 3$ the condition on the edges is implied by
the other two conditions.

The complete set of convex uniform 5-polytopes has not been determined. The known ones are:
* the Wythoffian polytopes of the irreducible reflection groups $A_5$ ($19$ polytopes),
  $B_5$ ($31$) and $D_5$ ($8$ not already in the $B_5$ family). A Wythoffian polytope is the
  convex hull of the orbit of a point under a finite reflection group;
* the prisms over the convex uniform 4-polytopes: the $45$ polychoral prisms not already counted
  (the prism over the tesseract is the 5-cube), the grand antiprism prism (the only known
  non-Wythoffian convex uniform 5-polytope), and the infinite family of duoprism prisms
  $\{p\}\times\{q\}\times\{\,\}$;
* the infinite duoprismatic families $\{q,r\}\times\{p\}$: Cartesian products of a convex uniform
  polyhedron and a regular polygon.

This gives $19 + 31 + 8 + 45 + 1 = 104$ known convex uniform 5-polytopes outside the infinite
families. The problem asks to find and classify the complete set of convex uniform 5-polytopes.

We formalise the statement that the known list is complete: every convex uniform 5-polytope in
$\mathbb{R}^5$ is Wythoffian, or a prism over a convex uniform 4-polytope, or the Cartesian
product of a convex uniform polyhedron and a regular polygon. Products are taken over all convex
uniform polytopes of the given dimensions (so, for instance, products of antiprisms or snub
polyhedra with regular polygons are included). Each of these three classes is closed under
similarities, so this is a statement about convex uniform 5-polytopes up to similarity. We also
record the literal open-ended form of the problem with `answer(sorry)`.

*References:*
- [Wikipedia, Uniform 5-polytope](https://en.wikipedia.org/wiki/uniform_5-polytope)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Open Problem Garden, Convex uniform 5-polytopes](http://www.openproblemgarden.org/op/convex_uniform_5_polytopes)
-/

open scoped EuclideanGeometry Pointwise

namespace Uniform5Polytope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A (convex) polytope in `E`: the convex hull of a finite set of points. -/
def IsPolytope (P : Set E) : Prop := ∃ s : Finset E, P = convexHull ℝ (s : Set E)

/-- The affine dimension of a set `P`, i.e. the dimension of its affine span. -/
noncomputable def affDim (P : Set E) : ℕ := Module.finrank ℝ (vectorSpan ℝ P)

/-- `F` is a `k`-dimensional face of the polytope `P`: a nonempty exposed subset of `P` (the set of
maximisers over `P` of a linear functional) of affine dimension `k`. All faces of a polytope are
exposed, so this captures all vertices (`k = 0`), edges (`k = 1`) and facets
(`k = affDim P - 1`). -/
def IsFace (P F : Set E) (k : ℕ) : Prop := F.Nonempty ∧ IsExposed ℝ P F ∧ affDim F = k

/-- `P` is vertex-transitive: for any two vertices (extreme points) `v`, `w` of `P` there is an
isometry `g` of `E` with `g '' P = P` and `g v = w`. -/
def IsVertexTransitive (P : Set E) : Prop :=
  ∀ v ∈ P.extremePoints ℝ, ∀ w ∈ P.extremePoints ℝ, ∃ g : E ≃ᵃⁱ[ℝ] E, g '' P = P ∧ g v = w

/-- All edges (one-dimensional faces) of `P` have the same length. -/
def HasEqualEdges (P : Set E) : Prop :=
  ∀ e₁ e₂, IsFace P e₁ 1 → IsFace P e₂ 1 → Metric.diam e₁ = Metric.diam e₂

/-- `P` is a convex uniform `d`-polytope. A uniform `0`-polytope is a point. For `d ≥ 1`, a uniform
`d`-polytope is a `d`-dimensional polytope that is vertex-transitive, has all edges of the same
length, and all of whose facets are uniform `(d - 1)`-polytopes.

For `d = 1` this gives segments and for `d = 2` exactly the regular polygons, so for `d ≥ 3` this
is the usual recursive definition of a uniform polytope: vertex-transitive with uniform facets
(the condition on edges is then automatic). The symmetries of a lower-dimensional polytope are
taken to be the isometries of `E` mapping it onto itself; since every isometry of its affine span
extends to an isometry of `E`, this agrees with the intrinsic notion. -/
def IsUniformPolytope : ℕ → Set E → Prop
  | 0, P => ∃ x, P = {x}
  | d + 1, P => IsPolytope P ∧ affDim P = d + 1 ∧ IsVertexTransitive P ∧ HasEqualEdges P ∧
      ∀ F, IsFace P F d → IsUniformPolytope d F

/-- A point is a uniform `0`-polytope. -/
@[category test, AMS 51 52]
theorem isUniformPolytope_zero_singleton (x : E) : IsUniformPolytope 0 ({x} : Set E) := ⟨x, rfl⟩

/-- A convex uniform `(d + 1)`-polytope is a polytope of dimension `d + 1`. -/
@[category API, AMS 51 52]
theorem IsUniformPolytope.isPolytope_and_affDim {d : ℕ} {P : Set E}
    (hP : IsUniformPolytope (d + 1) P) : IsPolytope P ∧ affDim P = d + 1 :=
  ⟨hP.1, hP.2.1⟩

variable [FiniteDimensional ℝ E]

/-- `g` is the reflection of `E` in an affine hyperplane `H`. -/
def IsHyperplaneReflection (g : E ≃ᵃⁱ[ℝ] E) : Prop :=
  ∃ (H : AffineSubspace ℝ E) (_ : Nonempty H),
    Module.finrank ℝ H.direction + 1 = Module.finrank ℝ E ∧ g = EuclideanGeometry.reflection H

/-- `G` is a finite reflection group: a finite group of isometries of `E` generated by reflections
in hyperplanes. -/
def IsFiniteReflectionGroup (G : Subgroup (E ≃ᵃⁱ[ℝ] E)) : Prop :=
  Finite G ∧ ∃ S : Set (E ≃ᵃⁱ[ℝ] E), (∀ g ∈ S, IsHyperplaneReflection g) ∧ G = Subgroup.closure S

/-- `P` is Wythoffian: it is the convex hull of the orbit of a point under a finite reflection
group (Wythoff's construction). The uniform polytopes of this form are exactly those obtained
from a ringed Coxeter diagram of a finite Coxeter group. -/
def IsWythoffian (P : Set E) : Prop :=
  ∃ (G : Subgroup (E ≃ᵃⁱ[ℝ] E)) (x : E), IsFiniteReflectionGroup G ∧
    P = convexHull ℝ (Set.range fun g : G => (g : E ≃ᵃⁱ[ℝ] E) x)

/-- `P` is the Cartesian product of a convex uniform `m`-polytope `A` and a convex uniform
`n`-polytope `B` lying in orthogonal subspaces, realised as the Minkowski sum `A + B` with
`A ⊆ U` and `B ⊆ Uᗮ`. The case `n = 1` is a (right) prism over `A`; the case `(m, n) = (3, 2)`
is a polyhedron-polygon duoprism. -/
def IsProductOfUniformPolytopes (m n : ℕ) (P : Set E) : Prop :=
  ∃ (U : Submodule ℝ E) (A B : Set E), A ⊆ U ∧ B ⊆ Uᗮ ∧
    IsUniformPolytope m A ∧ IsUniformPolytope n B ∧ P = A + B

/-- A point is Wythoffian (take the trivial reflection group). -/
@[category test, AMS 51 52]
theorem isWythoffian_singleton (x : E) : IsWythoffian ({x} : Set E) := by
  refine ⟨⊥, x, ⟨inferInstance, ∅, by simp, Subgroup.closure_empty.symm⟩, ?_⟩
  have : Set.range (fun g : (⊥ : Subgroup (E ≃ᵃⁱ[ℝ] E)) => (g : E ≃ᵃⁱ[ℝ] E) x) = {x} := by
    ext y
    simp only [Set.mem_range, Set.mem_singleton_iff]
    exact ⟨fun ⟨g, hg⟩ => by rw [← hg, show (g : E ≃ᵃⁱ[ℝ] E) = 1 from Subgroup.mem_bot.mp g.2]; rfl,
      fun h => ⟨1, by rw [h]; rfl⟩⟩
  rw [this, convexHull_singleton]

/--
**Convex uniform 5-polytopes**: find and classify the complete set of these shapes.

We state the conjecture that the known list is complete: every convex uniform 5-polytope is
* a Wythoffian polytope, i.e. the convex hull of the orbit of a point under a finite reflection
  group (the $19 + 31 + 8 = 58$ non-prismatic polytopes of the $A_5$, $B_5$ and $D_5$ families;
  reducible reflection groups only give prisms and duoprisms, which fall under the next two
  cases), or
* a prism over a convex uniform 4-polytope (the $45$ polychoral prisms, the grand antiprism prism
  and the duoprism prisms $\{p\}\times\{q\}\times\{\,\}$), or
* the Cartesian product of a convex uniform polyhedron and a regular polygon (the duoprismatic
  families $\{q,r\}\times\{p\}$).

Each of the three cases is invariant under similarities, so the statement classifies convex
uniform 5-polytopes up to similarity. It says that the list of $104$ known convex uniform
5-polytopes, together with the infinite prismatic families, is complete.
-/
@[category research open, AMS 51 52]
theorem uniform_5_polytope (P : Set (ℝ^5)) (hP : IsUniformPolytope 5 P) :
    IsWythoffian P ∨ IsProductOfUniformPolytopes 4 1 P ∨ IsProductOfUniformPolytopes 3 2 P := by
  sorry

/-- The problem in its original open-ended form: find the complete set of convex uniform
5-polytopes, as subsets of $\mathbb{R}^5$. This set is closed under similarities, so determining
it is the same as classifying convex uniform 5-polytopes up to similarity. -/
@[category research open, AMS 51 52]
theorem uniform_5_polytope.variants.find :
    {P : Set (ℝ^5) | IsUniformPolytope 5 P} = answer(sorry) := by
  sorry

end Uniform5Polytope
