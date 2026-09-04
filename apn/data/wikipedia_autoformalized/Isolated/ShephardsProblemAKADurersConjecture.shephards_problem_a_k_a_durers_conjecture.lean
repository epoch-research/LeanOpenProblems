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
# Shephard's problem (a.k.a. Dürer's conjecture)

Does every convex polyhedron have a net, or simple edge-unfolding?

A (compact) convex polyhedron is the boundary of the convex hull $K$ of finitely many points of
$\mathbb{R}^3$ which do not all lie in a plane, i.e. $K$ has nonempty interior. Cutting the
boundary of $K$ along a spanning tree $T$ of the edge graph of $K$ yields a surface $K_T$: the
disjoint union of the facets of $K$, glued back together along the edges that are not in $T$.
This surface is a flat topological disk, so it can be developed isometrically into the plane.
Such a development is an *edge unfolding* of $K$. It is *simple*, and its image is a *net*, if the
developing map $K_T \to \mathbb{R}^2$ is one-to-one, i.e. the unfolded faces do not overlap.

Shephard (1975) asked whether every convex polyhedron admits a simple edge unfolding. The
conjectured answer "yes" is known as Dürer's conjecture. The problem is open.

We follow the conventions of Ghomi and Barvinok–Ghomi: an unfolding of $K_T$ is a map to the
plane which preserves distances between points of each facet, and it is simple when it is
one-to-one on all of $K_T$. In particular two distinct points of $K_T$ (for instance two copies
of a cut vertex) may not touch in the plane. The cut tree must consist of genuine edges of $K$
(not pseudo-edges, and the facets are not subdivided).

*References:*
- [Wikipedia, Net (polyhedron)](https://en.wikipedia.org/wiki/Shephard%27s_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Sh75] Shephard, G. C., *Convex polytopes with convex nets*, Math. Proc. Cambridge Philos. Soc.
  78 (1975), 389–403.
- [Gh14] Ghomi, M., *Affine unfoldings of convex polyhedra*, Geom. Topol. 18 (2014), 3055–3090.
  [arXiv:1305.3231](https://arxiv.org/abs/1305.3231)
- [BG20] Barvinok, N. and Ghomi, M., *Pseudo-edge unfoldings of convex polyhedra*, Discrete
  Comput. Geom. 64 (2020), 671–689. [arXiv:1709.04944](https://arxiv.org/abs/1709.04944)
-/

open scoped EuclideanGeometry

namespace ShephardsProblemAKADurersConjecture

/-- `IsFacet K F` means that `F` is a facet (a two-dimensional face) of the convex polytope
`K ⊆ ℝ³`: `F` is an exposed face of `K` whose affine span is a plane. -/
def IsFacet (K F : Set ℝ³) : Prop :=
  IsExposed ℝ K F ∧ Module.finrank ℝ (vectorSpan ℝ F) = 2

/-- The type of facets of the convex polytope `K ⊆ ℝ³`. -/
abbrev Facet (K : Set ℝ³) : Type := {F : Set ℝ³ // IsFacet K F}

/-- The edge graph of the convex polytope `K ⊆ ℝ³`. Its vertices are the extreme points of `K`,
and two distinct vertices `v`, `w` are adjacent when the segment `[v, w]` is an exposed face of
`K`, i.e. an edge of `K`. -/
def edgeGraph (K : Set ℝ³) : SimpleGraph (K.extremePoints ℝ) where
  Adj v w := v ≠ w ∧ IsExposed ℝ K (segment ℝ (v : ℝ³) w)
  symm v w h := ⟨h.1.symm, segment_symm ℝ (v : ℝ³) w ▸ h.2⟩
  loopless _ h := h.1 rfl

/-- A point of the disjoint union of the facets of `K`: a facet `F` together with a point of `F`.
-/
abbrev FacetPoint (K : Set ℝ³) : Type := Σ F : Facet K, F.1

/-- The elementary gluing relation on `FacetPoint K` after cutting the boundary of `K` along the
subgraph `T` of its edge graph. Two facet points are directly glued when they are copies of the
same point `x` of `K`, and `x` lies on an edge `[v, w]` of `K` which is contained in both facets
and is *not* cut, i.e. `v` and `w` are not adjacent in `T`. -/
def Glued (K : Set ℝ³) (T : SimpleGraph (K.extremePoints ℝ)) (p q : FacetPoint K) : Prop :=
  (p.2 : ℝ³) = q.2 ∧ ∃ v w : K.extremePoints ℝ, (edgeGraph K).Adj v w ∧ ¬ T.Adj v w ∧
    segment ℝ (v : ℝ³) w ⊆ p.1.1 ∧ segment ℝ (v : ℝ³) w ⊆ q.1.1 ∧
    (p.2 : ℝ³) ∈ segment ℝ (v : ℝ³) w

/-- The cut surface `K_T`: the boundary of `K` cut along the subgraph `T` of its edge graph. It
is the quotient of the disjoint union of the facets of `K` by the equivalence relation generated
by `Glued K T`, so the copies of each uncut edge are glued together (and the copies of a vertex
are identified when they are connected through uncut edges). -/
def CutSurface (K : Set ℝ³) (T : SimpleGraph (K.extremePoints ℝ)) : Type :=
  Quotient (Relation.EqvGen.setoid (Glued K T))

/-- `IsSimpleEdgeUnfolding K T u` means that `u : K_T → ℝ²` is a simple (one-to-one) unfolding
of the boundary of `K` cut along `T`: `u` preserves distances between points of each facet, so
it develops every facet rigidly into the plane, and `u` is injective, so the developed facets do
not overlap (not even at boundary points which are distinct in `K_T`). -/
def IsSimpleEdgeUnfolding (K : Set ℝ³) (T : SimpleGraph (K.extremePoints ℝ))
    (u : CutSurface K T → ℝ²) : Prop :=
  Function.Injective u ∧
    ∀ (F : Facet K) (x y : F.1),
      dist (u (Quotient.mk _ ⟨F, x⟩)) (u (Quotient.mk _ ⟨F, y⟩)) = dist (x : ℝ³) y

/-- The convex polytope `K ⊆ ℝ³` has a net (a simple edge unfolding): there is a spanning tree
`T` of the edge graph of `K` such that the boundary of `K` cut along `T` admits a one-to-one
development into the plane. -/
def HasNet (K : Set ℝ³) : Prop :=
  ∃ T : SimpleGraph (K.extremePoints ℝ), T ≤ edgeGraph K ∧ T.IsTree ∧
    ∃ u : CutSurface K T → ℝ², IsSimpleEdgeUnfolding K T u

/-- **Shephard's problem (Dürer's conjecture).** Does every convex polyhedron have a net, or
simple edge-unfolding? That is, for every finite set of points of $\mathbb{R}^3$ whose convex hull
$K$ has nonempty interior, is there a spanning tree $T$ of the edge graph of $K$ such that the
boundary of $K$ cut along $T$ admits a one-to-one development into the plane $\mathbb{R}^2$
(a development which is isometric on each facet and injective, so that the facets do not
overlap)? The conjectured answer is yes. -/
theorem shephards_problem_a_k_a_durers_conjecture :
    ∀ S : Finset ℝ³, (interior (convexHull ℝ (S : Set ℝ³))).Nonempty →
      HasNet (convexHull ℝ (S : Set ℝ³)) := by
  sorry

end ShephardsProblemAKADurersConjecture

theorem ShephardsProblemAKADurersConjecture.shephards_problem_a_k_a_durers_conjecture.disproof : ¬ (type_of% @ShephardsProblemAKADurersConjecture.shephards_problem_a_k_a_durers_conjecture) := sorry
