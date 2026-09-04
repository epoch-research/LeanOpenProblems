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
# Barnette's conjecture

Barnette's conjecture states that every cubic bipartite three-connected planar graph has a
Hamiltonian cycle. Equivalently, every bipartite polyhedral graph with three edges per vertex is
Hamiltonian.

Mathlib has no notion of planar graph. This file defines a planar embedding of a simple graph as a
drawing in the Euclidean plane without crossings: vertices go to distinct points and edges go to
arcs that meet only at common endpoints.

*References:*
- [Wikipedia, Barnette's conjecture](https://en.wikipedia.org/wiki/Barnette%27s_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Ba69] Barnette, D., *Conjecture 5*. In Tutte, W. T. (ed.), Recent Progress in Combinatorics,
  Academic Press (1969).
-/

open SimpleGraph
open scoped EuclideanGeometry unitInterval

namespace BarnettesConjecture

variable {V : Type*}

/--
A planar embedding (a drawing without crossings) of a simple graph `G` in the Euclidean plane.

The vertices are sent to distinct points of the plane. Each edge is drawn as an arc, that is, a
continuous injective image of the unit interval `[0, 1]`, whose two ends are the images of the two
endpoints of the edge. No arc passes through the image of a vertex other than its own endpoints,
and two different arcs meet only at the images of vertices, which are then endpoints of both edges.
-/
structure PlanarEmbedding (G : SimpleGraph V) where
  /-- The position of each vertex in the plane. -/
  vertex : V → ℝ²
  /-- The arc drawing each edge. -/
  arc : G.edgeSet → I → ℝ²
  vertex_injective : Function.Injective vertex
  continuous_arc (e : G.edgeSet) : Continuous (arc e)
  arc_injective (e : G.edgeSet) : Function.Injective (arc e)
  /-- The ends of the arc of an edge are the images of the endpoints of that edge. -/
  arc_zero_one (e : G.edgeSet) :
    ∃ u v, (e : Sym2 V) = s(u, v) ∧ arc e 0 = vertex u ∧ arc e 1 = vertex v
  /-- An arc meets the image of a vertex only if that vertex is an endpoint of its edge. -/
  mem_of_vertex_mem_range (e : G.edgeSet) (w : V) : vertex w ∈ Set.range (arc e) → w ∈ (e : Sym2 V)
  /-- Two different arcs meet only at images of vertices. -/
  mem_range_vertex_of_mem_inter (e e' : G.edgeSet) (he : e ≠ e') (p : ℝ²)
    (hp : p ∈ Set.range (arc e) ∩ Set.range (arc e')) : p ∈ Set.range vertex

/-- A simple graph is planar if it has a planar embedding in the Euclidean plane. -/
def IsPlanar (G : SimpleGraph V) : Prop :=
  Nonempty (PlanarEmbedding G)

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/--
**Barnette's conjecture.**

Every cubic bipartite three-connected planar graph has a Hamiltonian cycle.

Here a finite simple graph is *cubic* if every vertex has degree $3$, *bipartite* if its vertices
can be coloured with two colours so that no edge is monochromatic, *three-connected* if it has more
than $3$ vertices and stays connected after the removal of any set of at most $2$ vertices, and
*planar* if it can be drawn in the Euclidean plane without crossings. A planar three-connected
graph is also called *polyhedral*.
-/
theorem barnettes_conjecture (hcubic : G.IsRegularOfDegree 3) (hbip : G.IsBipartite)
    (hconn : IsKConnected G 3) (hplanar : IsPlanar G) : G.IsHamiltonian := by
  sorry

end BarnettesConjecture

theorem BarnettesConjecture.barnettes_conjecture.disproof : ¬ (type_of% @BarnettesConjecture.barnettes_conjecture) := sorry
