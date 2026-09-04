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
# Word-representable near-triangulations

A graph $G = (V, E)$ is *word-representable* if there is a word $w$ over the alphabet $V$,
containing every letter of $V$, such that two distinct letters $x, y$ alternate in $w$ if and
only if $xy \in E$. Two letters alternate in $w$ if deleting all other letters from $w$ leaves a
word of the form $xyxy\dots$ or $yxyx\dots$.

Wikipedia's list of unsolved problems asks to characterise the word-representable
near-triangulations containing $K_4$, and remarks that "such a characterisation is known for
$K_4$-free planar graphs". The known result is Glen's theorem [Gl19]: a $K_4$-free
near-triangulation is word-representable if and only if it is $3$-colourable.
A *near-triangulation* is a planar graph in which every inner (bounded) face is a triangle;
the outer face is unrestricted. This file states that known result. The open problem itself
asks for a characterisation and is not stated here.

Since Mathlib has no notion of a plane graph, this file defines plane drawings directly:
vertices are distinct points of $\mathbb{R}^2$, edges are Jordan arcs between their endpoints,
and distinct arcs meet only in common endpoints. Faces are the connected components of the
complement of the drawing.

*References:*
- [Wikipedia, Word-representable graph](https://en.wikipedia.org/wiki/Word-representable_graph)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Gl19] M. E. Glen, *Colourability and word-representability of near-triangulations*,
  Pure Mathematics and Applications 28 (2019), no. 1, 70–76.
-/

namespace WordRepresentable2

open SimpleGraph
open scoped EuclideanGeometry

variable {V : Type*}

section Words

variable [DecidableEq V]

/--
The letters `x` and `y` *alternate* in the word `w` if deleting from `w` all letters other than
`x` and `y` leaves a word with no two consecutive equal letters, that is, a word of the form
`xyxy…` or `yxyx…`.
-/
def Alternate (w : List V) (x y : V) : Prop :=
  (w.filter fun z => z = x ∨ z = y).IsChain (· ≠ ·)

/--
The word `w` *represents* the graph `G`: every vertex of `G` occurs in `w`, and two distinct
vertices alternate in `w` if and only if they are adjacent in `G`.
-/
def Represents (w : List V) (G : SimpleGraph V) : Prop :=
  (∀ v, v ∈ w) ∧ ∀ x y, x ≠ y → (Alternate w x y ↔ G.Adj x y)

/-- A graph is *word-representable* if some word over its vertex set represents it. -/
def WordRepresentable (G : SimpleGraph V) : Prop :=
  ∃ w : List V, Represents w G

end Words

section Plane

/--
A *plane drawing* of the graph `G`, that is, a realisation of `G` as a plane graph: the vertices
are distinct points `pos v` of the plane, each edge `e` is drawn as a Jordan arc `arc e` joining
the positions of its two endpoints, the interior of an arc contains no vertex, and two distinct
arcs meet only in the positions of their common endpoints.
-/
structure PlaneEmbedding (G : SimpleGraph V) where
  /-- The point of the plane at which the vertex `v` is drawn. -/
  pos : V → ℝ²
  pos_injective : Function.Injective pos
  /-- The set of points of the plane forming the arc drawn for the edge `e`. -/
  arc : G.edgeSet → Set ℝ²
  /-- Each arc is a Jordan arc (the image of an injective path) between the positions of the
  two endpoints of its edge. -/
  exists_path (e : G.edgeSet) : ∃ u v, (e : Sym2 V) = s(u, v) ∧
    ∃ γ : Path (pos u) (pos v), Function.Injective γ ∧ Set.range γ = arc e
  /-- A vertex lies on an arc only if it is an endpoint of that edge. -/
  pos_mem_arc (v : V) (e : G.edgeSet) : pos v ∈ arc e → v ∈ (e : Sym2 V)
  /-- Two distinct arcs meet only in the positions of the common endpoints of their edges. -/
  arc_inter_arc (e e' : G.edgeSet) : e ≠ e' → ∀ p ∈ arc e ∩ arc e',
    ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (e' : Sym2 V) ∧ pos v = p

namespace PlaneEmbedding

variable {G : SimpleGraph V} (emb : PlaneEmbedding G)

/-- The set of points of the plane covered by the drawing. -/
def drawing : Set ℝ² :=
  Set.range emb.pos ∪ ⋃ e, emb.arc e

/--
The *face* of the drawing containing the point `p`: the connected component of `p` in the
complement of the drawing. It is empty when `p` lies on the drawing.
-/
def face (p : ℝ²) : Set ℝ² :=
  connectedComponentIn emb.drawingᶜ p

/--
A set `F` of points of the plane is a *triangular face* of the drawing if its frontier is exactly
the union of the arcs of three edges forming a triangle of `G`.
-/
def IsTriangleFace (F : Set ℝ²) : Prop :=
  ∃ (u v w : V) (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w),
    frontier F =
      emb.arc ⟨s(u, v), huv⟩ ∪ emb.arc ⟨s(v, w), hvw⟩ ∪ emb.arc ⟨s(u, w), huw⟩

end PlaneEmbedding

/--
A graph `G` is a *near-triangulation* if it admits a plane drawing in which every inner face,
that is, every bounded connected component of the complement of the drawing, is a triangle.
The unbounded (outer) face is unrestricted.
-/
def IsNearTriangulation (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbedding G, ∀ p ∉ emb.drawing,
    Bornology.IsBounded (emb.face p) → emb.IsTriangleFace (emb.face p)

/-- Any injective placement of the vertices is a plane drawing of the edgeless graph. -/
def PlaneEmbedding.bot {pos : V → ℝ²} (hpos : Function.Injective pos) :
    PlaneEmbedding (⊥ : SimpleGraph V) where
  pos := pos
  pos_injective := hpos
  arc e := absurd e.2 (by simp)
  exists_path e := absurd e.2 (by simp)
  pos_mem_arc _ e := absurd e.2 (by simp)
  arc_inter_arc e := absurd e.2 (by simp)

/-- The plane drawing of the graph with no vertices. -/
def PlaneEmbedding.empty : PlaneEmbedding (⊥ : SimpleGraph Empty) :=
  PlaneEmbedding.bot (pos := Empty.elim) fun a => a.elim

/-- The plane drawing of the graph with one vertex, placed at the origin. -/
def PlaneEmbedding.single : PlaneEmbedding (⊥ : SimpleGraph Unit) :=
  PlaneEmbedding.bot (pos := fun _ => (0 : ℝ²)) (Function.injective_of_subsingleton _)

end Plane

/--
**Glen's theorem** [Gl19]. Let $G$ be a $K_4$-free near-triangulation, that is, a finite plane
graph with no clique on four vertices in which every inner face is a triangle. Then $G$ is
word-representable if and only if $G$ is $3$-colourable.

This is the "characterisation known for $K_4$-free planar graphs" mentioned in the Wikipedia
list entry "Characterise word-representable near-triangulations containing the complete graph
$K_4$ (such a characterisation is known for $K_4$-free planar graphs)". The cited result [Gl19]
concerns $K_4$-free near-triangulations rather than all $K_4$-free planar graphs.
-/
theorem word_representable_2 [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : IsNearTriangulation G) (hK4 : G.CliqueFree 4) :
    WordRepresentable G ↔ G.Colorable 3 := by
  sorry

end WordRepresentable2

theorem WordRepresentable2.word_representable_2.disproof : ¬ (type_of% @WordRepresentable2.word_representable_2) := sorry
