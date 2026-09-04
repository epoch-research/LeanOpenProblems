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
# Strong Papadimitriou–Ratajczak conjecture

*References:*
- [Wikipedia, Greedy embedding § Planar graphs](https://en.wikipedia.org/wiki/Greedy_embedding%23Planar_graphs)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [PR05] Papadimitriou, C. H. and Ratajczak, D., *On a conjecture related to geometric routing*,
  Theoret. Comput. Sci. 344 (2005), 3–14.
- [NP13] Nöllenburg, M. and Prutkin, R., *Euclidean greedy drawings of trees*, Proc. 21st European
  Symposium on Algorithms (ESA 2013). [arXiv:1306.5224](https://arxiv.org/abs/1306.5224)
- [NPR16] Nöllenburg, M., Prutkin, R. and Rutter, I., *On self-approaching and increasing-chord
  drawings of 3-connected planar graphs*, J. Comput. Geom. 7 (2016), 47–69.
  [arXiv:1409.0315](https://arxiv.org/abs/1409.0315)

A *greedy embedding* of a graph in the Euclidean plane assigns a point to every vertex so that
for every two distinct vertices $x \neq t$ some neighbour $y$ of $x$ is strictly closer to $t$
than $x$ is. Papadimitriou and Ratajczak [PR05] conjectured that every polyhedral graph
(3-connected planar graph, equivalently the graph of a convex polyhedron) has a greedy embedding
in the Euclidean plane; this was proved by Leighton–Moitra and by Angelini–Frati–Grilli.
The greedy embeddings produced by these proofs need not be planar drawings.

The *strong* Papadimitriou–Ratajczak conjecture, which remains open, asserts that every
polyhedral graph has a *convex greedy embedding*: a planar straight-line drawing that is greedy
and in which every face, including the outer face, is a convex polygon [PR05, NP13, NPR16].

## Formalisation choices

- Drawings are straight-line: a drawing is a map from the vertices to $\mathbb{R}^2$, and every
  edge is drawn as the closed segment between the images of its endpoints. This is the setting
  of greedy embeddings, where only the vertex positions matter.
- Mathlib has no notion of planar graph. Since every graph considered here is finite and simple,
  we use Fáry's theorem and call a graph planar if it admits a planar straight-line drawing,
  that is, a drawing with distinct vertex positions in which no vertex lies on a non-incident
  edge and two distinct edges meet only in common endpoints.
- The faces of a planar straight-line drawing are the connected components of the complement of
  the drawing in the plane. A bounded face is a convex polygon if it is a convex set. The
  unbounded outer face is a convex polygon if its complement, the closed region enclosed by the
  outer boundary, is a convex set.
-/

open scoped EuclideanGeometry
open SimpleGraph

namespace StrongPapadimitriouRatajczakConjecture

variable {V : Type*} (G : SimpleGraph V) (p : V → ℝ²)

/-- The set of points of the plane covered by the straight-line drawing of `G` with vertex
positions `p`: the vertex points together with the closed segment joining the endpoints of every
edge. -/
def drawing : Set ℝ² :=
  Set.range p ∪ ⋃ (u : V) (v : V) (_ : G.Adj u v), segment ℝ (p u) (p v)

/-- `p` is a planar straight-line drawing of `G`: distinct vertices are drawn at distinct points,
no vertex lies on the segment drawing an edge unless it is an endpoint of that edge, and the
segments drawing two distinct edges meet only in the images of their common endpoints. -/
def IsPlanarStraightLineDrawing : Prop :=
  Function.Injective p ∧
  (∀ u v w, G.Adj u v → p w ∈ segment ℝ (p u) (p v) → w = u ∨ w = v) ∧
  (∀ u v x y, G.Adj u v → G.Adj x y → s(u, v) ≠ s(x, y) →
    segment ℝ (p u) (p v) ∩ segment ℝ (p x) (p y) ⊆ p '' ({u, v} ∩ {x, y}))

/-- A finite simple graph is *polyhedral* if it is 3-connected and planar. By Steinitz's theorem
these are exactly the graphs of vertices and edges of convex polyhedra. Planarity is expressed,
via Fáry's theorem, as the existence of a planar straight-line drawing. Note that
`G.IsKConnected 3` requires more than three vertices. -/
def IsPolyhedral [Fintype V] : Prop :=
  G.IsKConnected 3 ∧ ∃ p : V → ℝ², IsPlanarStraightLineDrawing G p

/-- The vertex positions `p` form a *greedy embedding* of `G` in the Euclidean plane: for every
two distinct vertices $x \neq t$ there is a neighbour $y$ of $x$ with $d(y, t) < d(x, t)$. -/
def IsGreedy : Prop :=
  ∀ x t, x ≠ t → ∃ y, G.Adj x y ∧ dist (p y) (p t) < dist (p x) (p t)

/-- Every face of the drawing of `G` with vertex positions `p` is a convex polygon. The faces are
the connected components of the complement of the drawing. A bounded face is required to be a
convex set; the unbounded (outer) face is required to have convex complement, i.e. the closed
region enclosed by the outer boundary is convex. -/
def HasConvexFaces : Prop :=
  ∀ x ∉ drawing G p,
    (Bornology.IsBounded (connectedComponentIn (drawing G p)ᶜ x) →
      Convex ℝ (connectedComponentIn (drawing G p)ᶜ x)) ∧
    (¬ Bornology.IsBounded (connectedComponentIn (drawing G p)ᶜ x) →
      Convex ℝ (connectedComponentIn (drawing G p)ᶜ x)ᶜ)

/-- `p` is a *convex greedy embedding* of `G`: a planar straight-line drawing of `G` in which
every face (including the outer face) is a convex polygon and which is greedy. -/
def IsConvexGreedyEmbedding : Prop :=
  IsPlanarStraightLineDrawing G p ∧ HasConvexFaces G p ∧ IsGreedy G p

/-- A greedy embedding of the complete graph is given by any injective vertex placement. -/
@[category test, AMS 5 52]
theorem isGreedy_top (hp : Function.Injective p) : IsGreedy (⊤ : SimpleGraph V) p := by
  intro x t hxt
  exact ⟨t, hxt, by simpa using dist_pos.mpr (hp.ne hxt)⟩

/-- The empty graph on at least two vertices has no greedy embedding. -/
@[category test, AMS 5 52]
theorem not_isGreedy_bot [Nontrivial V] : ¬ IsGreedy (⊥ : SimpleGraph V) p := by
  intro h
  obtain ⟨x, t, hxt⟩ := exists_pair_ne V
  obtain ⟨y, hy, -⟩ := h x t hxt
  exact hy

/-- A greedy embedding places distinct vertices at distinct points. -/
@[category API, AMS 5 52]
theorem IsGreedy.injective {G : SimpleGraph V} {p : V → ℝ²} (h : IsGreedy G p) :
    Function.Injective p := by
  intro x t hxt
  by_contra hne
  obtain ⟨y, -, hy⟩ := h x t hne
  rw [hxt, _root_.dist_self] at hy
  exact absurd hy (not_lt.mpr dist_nonneg)

/-- Any injective vertex placement is a planar straight-line drawing of the empty graph. -/
@[category test, AMS 5 52]
theorem isPlanarStraightLineDrawing_bot (hp : Function.Injective p) :
    IsPlanarStraightLineDrawing (⊥ : SimpleGraph V) p :=
  ⟨hp, fun _ _ _ h => h.elim, fun _ _ _ _ h => h.elim⟩

/-- A graph on at most three vertices is not polyhedral. -/
@[category test, AMS 5 52]
theorem not_isPolyhedral_of_card_le [Fintype V] (h : Fintype.card V ≤ 3) : ¬ IsPolyhedral G :=
  fun hG => not_isKConnected_of_card_le h hG.1

/-- **Strong Papadimitriou–Ratajczak conjecture** [PR05]. Every polyhedral graph, i.e. every
finite simple 3-connected planar graph, has a convex greedy embedding in the Euclidean plane:
a planar straight-line drawing in which every face (including the outer face) is a convex
polygon and such that for every two distinct vertices $x \neq t$ some neighbour $y$ of $x$
satisfies $d(y, t) < d(x, t)$. -/
@[category research open, AMS 5 52 68]
theorem strong_papadimitriou_ratajczak_conjecture [Fintype V] (hG : IsPolyhedral G) :
    ∃ p : V → ℝ², IsConvexGreedyEmbedding G p := by
  sorry

end StrongPapadimitriouRatajczakConjecture
