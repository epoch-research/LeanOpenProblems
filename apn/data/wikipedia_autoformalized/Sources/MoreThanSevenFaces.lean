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
# Polyhedra with more than seven pairwise adjacent faces

The tetrahedron ($4$ faces, genus $0$) and the Szilassi polyhedron ($7$ hexagonal faces,
genus $1$) are the only known polyhedra in which every face shares an edge with every other
face. If a polyhedron with $f$ faces and $h$ holes has this property, then Euler's formula
gives $h \geq (f-4)(f-3)/12$, with equality when each vertex has degree $3$ and each pair of
faces shares exactly one edge. The next candidate is $f = 12$, $h = 6$, and it is not known
whether such a polyhedron can be realised geometrically in $\mathbb{R}^3$ without
self-intersections (rather than as an abstract polytope).

Wikipedia asks: *Is there a non-convex polyhedron without self-intersections with more than
seven faces, all of which share an edge with each other?*

Here a *polyhedron* is a finite set of *faces*, each a planar simple (not necessarily convex)
polygon in $\mathbb{R}^3$, such that two distinct faces meet only along their boundaries, faces
sharing an edge are not coplanar, and the union of the faces is a connected closed surface
(a compact topological $2$-manifold without boundary). The last condition is what "without
self-intersections" means: the surface is embedded in $\mathbb{R}^3$. Two faces *share an edge*
if their intersection contains a line segment of positive length.

*References:*
- [Wikipedia, Szilassi polyhedron](https://en.wikipedia.org/wiki/Szilassi_polyhedron)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Sz86] Szilassi, L., *Regular toroids*, Structural Topology 13 (1986).
  http://www-iri.upc.es/people/ros/StructuralTopology/ST13/st13-06-a3-ocr.pdf
- [GS09] Grünbaum, B. and Szilassi, L., *Geometric realizations of special toroidal complexes*,
  Contributions to Discrete Mathematics 4 (2009). https://doi.org/10.11575/cdm.v4i1.61986
- [AKKLSVW24] Arseneva, E., Kleist, L., Klemz, B., Löffler, M., Schulz, A., Vogtenhuber, B.
  and Wolff, A., *Adjacency graphs of polyhedral surfaces*, Discrete & Computational Geometry
  (2024). https://doi.org/10.1007/s00454-023-00537-6
-/

namespace MoreThanSevenFaces

open scoped EuclideanGeometry

/--
A set $F \subseteq \mathbb{R}^3$ is a *polygon* (a simple, not necessarily convex, planar polygon
together with its interior) if it lies in a plane, is homeomorphic to a closed disk, and its
boundary relative to that plane is a finite union of line segments.
-/
def IsPolygon (F : Set ℝ³) : Prop :=
  Coplanar ℝ F ∧
  Nonempty (F ≃ₜ Metric.closedBall (0 : ℝ²) 1) ∧
  ∃ E : Finset (ℝ³ × ℝ³), intrinsicFrontier ℝ F = ⋃ e ∈ E, segment ℝ e.1 e.2

/-- Two faces *share an edge* if their intersection contains a line segment of positive
length (and not merely a vertex). -/
def SharesEdge (F G : Set ℝ³) : Prop :=
  ∃ a b : ℝ³, a ≠ b ∧ segment ℝ a b ⊆ F ∩ G

/--
A finite set `faces` of subsets of $\mathbb{R}^3$ is a *polyhedron without self-intersections*
if
- every face is a planar simple polygon (`IsPolygon`);
- two distinct faces meet only along their boundaries;
- two faces sharing an edge are not coplanar (so faces are genuine faces, not pieces of a
  larger planar face);
- the union of the faces is connected;
- the union of the faces is a topological $2$-manifold without boundary (it is automatically
  compact). Together with the previous conditions this says that the surface is embedded in
  $\mathbb{R}^3$: faces meet only along common edges and vertices, every edge lies in exactly
  two faces, and the faces around each vertex form a single cycle.
-/
structure IsPolyhedron (faces : Finset (Set ℝ³)) : Prop where
  isPolygon : ∀ F ∈ faces, IsPolygon F
  inter_subset_frontier : ∀ F ∈ faces, ∀ G ∈ faces, F ≠ G →
    F ∩ G ⊆ intrinsicFrontier ℝ F ∩ intrinsicFrontier ℝ G
  not_coplanar : ∀ F ∈ faces, ∀ G ∈ faces, F ≠ G → SharesEdge F G →
    ¬ Coplanar ℝ (F ∪ G)
  isConnected : IsConnected (⋃₀ (faces : Set (Set ℝ³)))
  chartedSpace : Nonempty (ChartedSpace ℝ² (⋃₀ (faces : Set (Set ℝ³))))

/-- A polyhedron is *convex* if its surface is the boundary of a convex set. -/
def IsConvexPolyhedron (faces : Finset (Set ℝ³)) : Prop :=
  ∃ K : Set ℝ³, Convex ℝ K ∧ frontier K = ⋃₀ (faces : Set (Set ℝ³))

/-- Sharing an edge is a symmetric relation. -/
@[category API, AMS 51 52]
theorem SharesEdge.symm {F G : Set ℝ³} (h : SharesEdge F G) : SharesEdge G F := by
  obtain ⟨a, b, hab, h⟩ := h
  exact ⟨a, b, hab, Set.inter_comm F G ▸ h⟩

/-- Two faces sharing an edge have nonempty intersection. -/
@[category API, AMS 51 52]
theorem SharesEdge.nonempty_inter {F G : Set ℝ³} (h : SharesEdge F G) : (F ∩ G).Nonempty := by
  obtain ⟨a, b, -, h⟩ := h
  exact ⟨a, h (left_mem_segment ℝ a b)⟩

/-- Two faces whose intersection has at most one point do not share an edge. -/
@[category test, AMS 51 52]
theorem not_sharesEdge_of_subsingleton {F G : Set ℝ³} (h : (F ∩ G).Subsingleton) :
    ¬ SharesEdge F G := by
  rintro ⟨a, b, hab, hs⟩
  exact hab (h (hs (left_mem_segment ℝ a b)) (hs (right_mem_segment ℝ a b)))

/-- A polygon is nonempty. -/
@[category API, AMS 51 52]
theorem IsPolygon.nonempty {F : Set ℝ³} (h : IsPolygon F) : F.Nonempty := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  exact ⟨e.symm ⟨0, Metric.mem_closedBall_self zero_le_one⟩, Subtype.coe_prop _⟩

/-- The empty set is not a polygon. -/
@[category test, AMS 51 52]
theorem not_isPolygon_empty : ¬ IsPolygon (∅ : Set ℝ³) := fun h ↦ by
  simpa using h.nonempty

/--
Is there a non-convex polyhedron without self-intersections with more than seven faces, all of
which share an edge with each other?

Here a polyhedron is a finite set of planar simple polygonal faces forming an embedded closed
surface in $\mathbb{R}^3$ (`IsPolyhedron`), it is convex if its surface bounds a convex set
(`IsConvexPolyhedron`), and two faces share an edge if their intersection contains a segment of
positive length (`SharesEdge`).

The only known polyhedra all of whose faces are pairwise adjacent are the tetrahedron and the
Szilassi polyhedron. (Non-convexity is automatic for more than seven faces, since Euler's formula
forces such a polyhedron to have positive genus; it is included to match the statement.)
-/
@[category research open, AMS 51 52]
theorem more_than_seven_faces :
    answer(sorry) ↔ ∃ faces : Finset (Set ℝ³), 7 < faces.card ∧ IsPolyhedron faces ∧
      ¬ IsConvexPolyhedron faces ∧
      ∀ F ∈ faces, ∀ G ∈ faces, F ≠ G → SharesEdge F G := by
  sorry

end MoreThanSevenFaces
