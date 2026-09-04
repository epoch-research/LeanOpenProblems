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
# Harborth's conjecture

Harborth's conjecture states that every planar graph can be drawn with integer edge lengths:
every (finite, simple) planar graph has a planar drawing in the Euclidean plane in which every
edge is a straight line segment of integer length. Such a drawing is also called an
*integral Fáry embedding*, since (if true) the conjecture strengthens Fáry's theorem on the
existence of planar straight-line drawings.

Mathlib has no notion of a planar graph, so this file defines planar drawings explicitly.
A *planar drawing* of a graph maps vertices to distinct points of the plane and edges to simple
arcs joining the images of their endpoints, so that an arc contains no vertex other than its
endpoints and two distinct arcs meet only in common endpoints. A graph is *planar* if it has a
planar drawing. A *planar straight-line drawing* is a planar drawing in which the arc of every
edge is the closed segment between the images of its endpoints.

*References:*
- [Wikipedia, Harborth's conjecture](https://en.wikipedia.org/wiki/Harborth%27s_conjecture)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [KH01] Kemnitz, A. and Harborth, H., *Plane integral drawings of planar graphs*,
  Discrete Mathematics 236 (2001), 191–195.
  [doi:10.1016/S0012-365X(00)00442-8](https://doi.org/10.1016/S0012-365X(00)00442-8)
-/

namespace HarborthsConjecture

open scoped EuclideanGeometry

variable {V : Type*} (G : SimpleGraph V)

/--
`IsPlanarDrawing G f arc` says that `f` and `arc` form a planar drawing of `G` in the plane:
* the vertices are mapped injectively to points `f v` of the plane;
* the edge `s(u, v)` is drawn as the set `arc s(u, v)`, which is a simple arc from `f u` to `f v`,
  i.e. the range of an injective path from `f u` to `f v`;
* the arc of an edge passes through no vertex other than its two endpoints;
* the arcs of two distinct edges meet only in the images of their common endpoints.
-/
structure IsPlanarDrawing (f : V → ℝ²) (arc : Sym2 V → Set ℝ²) : Prop where
  injective : Function.Injective f
  exists_path : ∀ u v, G.Adj u v →
    ∃ γ : Path (f u) (f v), Function.Injective γ ∧ Set.range γ = arc s(u, v)
  notMem_arc : ∀ u v w, G.Adj u v → w ≠ u → w ≠ v → f w ∉ arc s(u, v)
  inter_subset : ∀ u v u' v', G.Adj u v → G.Adj u' v' → s(u, v) ≠ s(u', v') →
    arc s(u, v) ∩ arc s(u', v') ⊆ f '' (({u, v} : Set V) ∩ {u', v'})

/-- A graph is planar if it has a planar drawing in the plane. -/
def IsPlanar : Prop :=
  ∃ (f : V → ℝ²) (arc : Sym2 V → Set ℝ²), IsPlanarDrawing G f arc

/-- The straight-line arcs of a vertex placement `f`: the unordered pair `s(u, v)` is sent to the
closed segment between `f u` and `f v`. -/
def segmentArcs (f : V → ℝ²) : Sym2 V → Set ℝ² :=
  Sym2.lift ⟨fun u v => segment ℝ (f u) (f v), fun _ _ => segment_symm ℝ _ _⟩

/-- `IsPlanarStraightLineDrawing G f` says that placing the vertices of `G` at the points `f v`
and drawing every edge as a straight segment gives a planar drawing of `G`
(a *Fáry embedding* of `G`). -/
def IsPlanarStraightLineDrawing (f : V → ℝ²) : Prop :=
  IsPlanarDrawing G f (segmentArcs f)

variable {G}

variable (G)

/--
**Harborth's conjecture.** Every planar graph can be drawn with integer edge lengths: every
finite planar graph $G$ has a planar drawing in the plane in which every edge is a straight
line segment whose Euclidean length is an integer.
-/
theorem harborths_conjecture [Fintype V] (hG : IsPlanar G) :
    ∃ f : V → ℝ², IsPlanarStraightLineDrawing G f ∧
      ∀ u v, G.Adj u v → ∃ n : ℤ, dist (f u) (f v) = n := by
  sorry

end HarborthsConjecture

theorem HarborthsConjecture.harborths_conjecture.disproof : ¬ (type_of% @HarborthsConjecture.harborths_conjecture) := sorry
