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
# In parallelohedron: the Voronoi conjecture

A *parallelohedron* (or *parallelotope*) is a convex $d$-dimensional polytope $P$ that tiles
$\mathbb{R}^d$ by translated copies of itself. The Dirichlet–Voronoi cell of a lattice
$\Lambda \subseteq \mathbb{R}^d$ (the set of points at least as close to the origin as to any other
lattice point) is always a parallelohedron. The **Voronoi conjecture** asserts the converse up to
affine transformations: every parallelohedron is an affine image of the Dirichlet–Voronoi cell of
some lattice.

For $d = 3$ this says that every parallelohedron can be made into a plesiohedron (here, the Voronoi
cell of a lattice) by an affine transformation. Delaunay proved this in 1929 for $d = 3$ and
$d = 4$, Garber proved it for $d = 5$, and it is open for $d \ge 6$.

*References:*
- [Wikipedia: Parallelohedron](https://en.wikipedia.org/wiki/parallelohedron)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [arXiv:1906.05193](https://arxiv.org/abs/1906.05193), A. Garber, *Voronoi conjecture for
  five-dimensional parallelohedra*.
-/

open scoped EuclideanGeometry Pointwise

namespace InParallelohedron

variable {d : ℕ}

/-- A set $P \subseteq \mathbb{R}^d$ *tiles $\mathbb{R}^d$ by translations* if there is a set $T$ of
translation vectors such that the translates $t + P$, $t \in T$, cover $\mathbb{R}^d$ and have
pairwise disjoint interiors. -/
def TilesByTranslations (P : Set (ℝ^d)) : Prop :=
  ∃ T : Set (ℝ^d), (⋃ t ∈ T, t +ᵥ P) = Set.univ ∧
    T.Pairwise fun s t => Disjoint (interior (s +ᵥ P)) (interior (t +ᵥ P))

/-- A *parallelohedron* in $\mathbb{R}^d$ is a $d$-dimensional convex polytope, i.e. the convex hull
of a finite set of points with nonempty interior, that tiles $\mathbb{R}^d$ by translations.
The nonempty interior condition expresses that the polytope is genuinely $d$-dimensional. -/
def IsParallelohedron (P : Set (ℝ^d)) : Prop :=
  (∃ S : Finset (ℝ^d), P = convexHull ℝ ↑S) ∧ (interior P).Nonempty ∧ TilesByTranslations P

/-- The (closed) *Dirichlet–Voronoi cell* of the origin with respect to a set
$\Lambda \subseteq \mathbb{R}^d$: the points of $\mathbb{R}^d$ that are at least as close to $0$ as
to any point of $\Lambda$. When $\Lambda$ is a lattice, this is the Dirichlet–Voronoi polytope of
$\Lambda$. -/
def dirichletVoronoiCell (Λ : Set (ℝ^d)) : Set (ℝ^d) :=
  {x | ∀ l ∈ Λ, dist x 0 ≤ dist x l}

/-- The **Voronoi conjecture** in dimension $d$: for every parallelohedron $P \subseteq \mathbb{R}^d$
there exist a full-rank lattice $\Lambda \subseteq \mathbb{R}^d$ and an affine transformation
$\mathcal{A}$ of $\mathbb{R}^d$ such that $\mathcal{A}(P)$ is the Dirichlet–Voronoi cell of
$\Lambda$. -/
def VoronoiConjectureDim (d : ℕ) : Prop :=
  ∀ P : Set (ℝ^d), IsParallelohedron P →
    ∃ (Λ : Submodule ℤ (ℝ^d)) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ) (A : ℝ^d ≃ᵃ[ℝ] ℝ^d),
      A '' P = dirichletVoronoiCell Λ

/-- The three-dimensional case of the Voronoi conjecture: every parallelohedron can be made into a
plesiohedron, i.e. the Dirichlet–Voronoi cell of a lattice, by an affine transformation.
Proved by Delaunay in 1929. -/
theorem in_parallelohedron.parts.ii.variants.dim_three : VoronoiConjectureDim 3 := by
  sorry

end InParallelohedron

theorem InParallelohedron.in_parallelohedron.parts.ii.variants.dim_three.disproof : ¬ (type_of% @InParallelohedron.in_parallelohedron.parts.ii.variants.dim_three) := sorry
