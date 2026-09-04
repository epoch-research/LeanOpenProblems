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
# Grünbaum's conjecture on spherical polyhedra that tile space by translation

Can every spherical non-convex polyhedron that tiles space by translation have its faces grouped
into patches with the same combinatorial structure as a parallelohedron?

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Parallelohedron](https://en.wikipedia.org/wiki/parallelohedron)
- [Gr10] Grünbaum, Branko, *The Bilinski dodecahedron and assorted parallelohedra, zonohedra,
  monohedra, isozonohedra, and otherhedra*, The Mathematical Intelligencer 32 (2010), 5–15.
  [doi:10.1007/s00283-010-9138-7](https://doi.org/10.1007/s00283-010-9138-7)
-/

open scoped EuclideanGeometry Pointwise

namespace CanEverySphericalNonConvexPolyhedronThatTilesSpaceByTranslationHaveI

/-- A set `P ⊆ ℝ³` *tiles space by translation* if some family of translates of `P` covers `ℝ³`
and any two distinct translates in the family have disjoint interiors. -/
def TilesByTranslation (P : Set ℝ³) : Prop :=
  ∃ T : Set ℝ³, (⋃ t ∈ T, t +ᵥ P) = Set.univ ∧
    T.Pairwise fun s t => Disjoint (interior (s +ᵥ P)) (interior (t +ᵥ P))

/-- A (planar, not necessarily convex) *polygon* in `ℝ³`: a finite union of non-degenerate
triangles that lies in a plane (its affine span is two-dimensional) and is homeomorphic to a
closed disk. Equivalently, it is the region of a plane bounded by a simple closed polygonal
curve. -/
def IsPolygon (f : Set ℝ³) : Prop :=
  (∃ s : Finset (Fin 3 → ℝ³), (∀ t ∈ s, AffineIndependent ℝ t) ∧
    f = ⋃ t ∈ s, convexHull ℝ (Set.range t)) ∧
  Module.finrank ℝ (affineSpan ℝ f).direction = 2 ∧
  Nonempty (f ≃ₜ Metric.closedBall (0 : ℝ²) 1)

/-- A *spherical polyhedron*: a compact solid `solid ⊆ ℝ³` which is the closure of its interior
and whose boundary surface is homeomorphic to the $2$-sphere, together with a finite family of
`faces`. The faces are polygons with pairwise disjoint relative interiors whose union is the
boundary surface. Convexity is **not** assumed, so the faces may be non-convex polygons and
the solid may have re-entrant edges and vertices. -/
structure SphericalPolyhedron where
  /-- The solid body of the polyhedron. -/
  solid : Set ℝ³
  /-- The faces of the polyhedron. -/
  faces : Finset (Set ℝ³)
  isCompact : IsCompact solid
  closure_interior : closure (interior solid) = solid
  sphere : Nonempty (frontier solid ≃ₜ Metric.sphere (0 : ℝ³) 1)
  isPolygon : ∀ f ∈ faces, IsPolygon f
  sUnion_faces : ⋃₀ (faces : Set (Set ℝ³)) = frontier solid
  pairwise_disjoint : (faces : Set (Set ℝ³)).Pairwise fun f g =>
    Disjoint (intrinsicInterior ℝ f) (intrinsicInterior ℝ g)

/-- A grouping of the faces of `P` into *patches* (unions of connected subsets of faces):
a partition `𝒬` of the faces of `P` into nonempty blocks such that the union of the faces in each
block is connected. The patch corresponding to a block `q` is the union `⋃₀ q` of its faces. -/
structure SphericalPolyhedron.IsPatchDecomposition (P : SphericalPolyhedron)
    (𝒬 : Finset (Finset (Set ℝ³))) : Prop where
  nonempty : ∀ q ∈ 𝒬, q.Nonempty
  subset_faces : ∀ q ∈ 𝒬, q ⊆ P.faces
  existsUnique_mem : ∀ f ∈ P.faces, ∃! q, q ∈ 𝒬 ∧ f ∈ q
  isConnected : ∀ q ∈ 𝒬, IsConnected (⋃₀ (q : Set (Set ℝ³)))

/-- The patches of a grouping `𝒬` of the faces of a polyhedron, as subsets of its boundary
surface: the unions of the blocks of `𝒬`. -/
def patches (𝒬 : Finset (Finset (Set ℝ³))) : Set (Set ℝ³) :=
  (fun q : Finset (Set ℝ³) => ⋃₀ (q : Set (Set ℝ³))) '' 𝒬

/-- A *parallelohedron*: a convex polyhedron in `ℝ³` (the convex hull of a finite set, with
nonempty interior) that tiles space by translation. By the theorems of Fedorov, Minkowski,
Venkov and McMullen these are precisely the parallelepipeds, hexagonal prisms, rhombic
dodecahedra, elongated dodecahedra and truncated octahedra (up to combinatorial equivalence),
and every such convex polyhedron also tiles space face-to-face by a lattice of translations. -/
def IsParallelohedron (Q : Set ℝ³) : Prop :=
  (∃ s : Finset ℝ³, Q = convexHull ℝ (s : Set ℝ³)) ∧ (interior Q).Nonempty ∧
    TilesByTranslation Q

/-- `F` is a *facet* (a two-dimensional face) of the convex polyhedron `Q`: an exposed subset
of `Q` whose affine span is a plane. -/
def IsFacet (Q F : Set ℝ³) : Prop :=
  IsExposed ℝ Q F ∧ Module.finrank ℝ (affineSpan ℝ F).direction = 2

/-- The decomposition of the surface `S ⊆ ℝ³` into the cells `𝒞` has *the same combinatorial
structure* as the decomposition of the surface `T ⊆ ℝ³` into the cells `𝒟` if there is a
homeomorphism `φ` from `S` onto `T` under which `c ↦ φ '' c` is a bijection from `𝒞` onto
`𝒟`. Such a homeomorphism carries intersections of cells to intersections of cells, so it
induces an isomorphism of the face structures (cells, edges, vertices, and their incidences).

Since the surfaces considered here are compact, a continuous injection `φ` on `S` with
`φ '' S = T` is automatically a homeomorphism from `S` onto `T`. -/
def CombinatoriallyEquivalent (S : Set ℝ³) (𝒞 : Set (Set ℝ³)) (T : Set ℝ³)
    (𝒟 : Set (Set ℝ³)) : Prop :=
  ∃ φ : ℝ³ → ℝ³, ContinuousOn φ S ∧ S.InjOn φ ∧ φ '' S = T ∧
    Set.BijOn (fun c => φ '' c) 𝒞 𝒟

@[category API, AMS 51 52]
theorem tilesByTranslation_univ : TilesByTranslation Set.univ :=
  ⟨{0}, by simp, Set.pairwise_singleton _ _⟩

@[category API, AMS 51 52]
theorem IsFacet.subset {Q F : Set ℝ³} (h : IsFacet Q F) : F ⊆ Q :=
  h.1.subset

@[category API, AMS 51 52]
theorem IsParallelohedron.convex {Q : Set ℝ³} (h : IsParallelohedron Q) : Convex ℝ Q := by
  obtain ⟨⟨s, rfl⟩, -, -⟩ := h
  exact convex_convexHull ℝ _

@[category API, AMS 51 52]
theorem IsParallelohedron.isCompact {Q : Set ℝ³} (h : IsParallelohedron Q) : IsCompact Q := by
  obtain ⟨⟨s, rfl⟩, -, -⟩ := h
  exact s.finite_toSet.isCompact_convexHull

/-- **Grünbaum's conjecture.** Can every spherical non-convex polyhedron that tiles space by
translation have its faces grouped into patches with the same combinatorial structure as a
parallelohedron?

Precisely: let $P$ be a non-convex polyhedron in $\mathbb{R}^3$ whose boundary surface is
homeomorphic to a sphere and whose translated copies tile space. Is it always possible to
partition the faces of $P$ into patches (connected unions of faces) so that the combinatorial
structure of the patches (as pseudo-faces of the surface of $P$) is that of the faces of one of
the five Fedorov parallelohedra, i.e. so that there is a homeomorphism from the surface of $P$
onto the surface of a parallelohedron $Q$ taking the patches onto the facets of $Q$?

The conjectured answer is yes. Following the statement, only non-convex polyhedra are
considered; for a convex polyhedron $P$ the conclusion holds trivially (take $Q = P$ and group
the faces of $P$ by the facet containing them), so the statement is equivalent to Grünbaum's
original formulation [Gr10] for all polyhedra that are topologically spheres and tile space by
translation. -/
@[category research open, AMS 51 52]
theorem can_every_spherical_non_convex_polyhedron_that_tiles_space_by_translation_have_i :
    answer(sorry) ↔
      ∀ P : SphericalPolyhedron, ¬ Convex ℝ P.solid → TilesByTranslation P.solid →
        ∃ 𝒬 : Finset (Finset (Set ℝ³)), P.IsPatchDecomposition 𝒬 ∧
          ∃ Q : Set ℝ³, IsParallelohedron Q ∧
            CombinatoriallyEquivalent (frontier P.solid) (patches 𝒬)
              (frontier Q) {F | IsFacet Q F} := by
  sorry

end CanEverySphericalNonConvexPolyhedronThatTilesSpaceByTranslationHaveI
