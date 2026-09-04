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
# Voronoi diagram: Voronoi's conjecture on parallelohedra

A *parallelohedron* is a convex polytope $P \subseteq \mathbb{R}^d$ with nonempty interior whose
translates tile $\mathbb{R}^d$. The *Voronoi diagram* of a lattice $L \subseteq \mathbb{R}^d$
(in the Euclidean metric) is the tiling of $\mathbb{R}^d$ by the translates $p + V_L$, $p \in L$,
of the Dirichlet–Voronoi cell
$$V_L = \{x \in \mathbb{R}^d : \|x\| \le \|x - p\| \text{ for all } p \in L\}$$
of the origin. Voronoi (1908) conjectured that every parallelohedron is the image of the
Dirichlet–Voronoi cell of some lattice under an affine transformation. Equivalently, for every
parallelohedron $P$ there are an affine transformation $A$ of $\mathbb{R}^d$ and a lattice $L$
such that $A$ carries a tiling of $\mathbb{R}^d$ by translates of $P$ (namely the lattice tiling
$\{A^{-1}(p + V_L) : p \in L\}$) onto the Voronoi diagram of $L$.

The conjecture is known to hold for $d \le 5$ and is open for $d \ge 6$.

*References:*
- [Wikipedia, *Voronoi diagram*](https://en.wikipedia.org/wiki/Voronoi_diagram)
- [Wikipedia, *Parallelohedron*](https://en.wikipedia.org/wiki/Parallelohedron)
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- G. Voronoi, *Nouvelles applications des paramètres continus à la théorie des formes
  quadratiques. Deuxième mémoire. Recherches sur les paralléloèdres primitifs*,
  J. Reine Angew. Math. 134 (1908), 198–287 and 136 (1909), 67–181.
-/

open scoped EuclideanGeometry Pointwise

namespace VoronoiDiagram

variable {d : ℕ}

/-- A subset `P` of `ℝ^d` is a **convex polytope** if it is the convex hull of a finite set of
points. Such a set is automatically compact and convex. -/
def IsConvexPolytope (P : Set (ℝ^d)) : Prop :=
  ∃ s : Finset (ℝ^d), P = convexHull ℝ (s : Set (ℝ^d))

/-- The translates `t +ᵥ P`, `t ∈ T`, of a set `P ⊆ ℝ^d` form a **tiling** of `ℝ^d` if they
cover `ℝ^d` and have pairwise disjoint interiors. -/
def IsTilingByTranslates (P T : Set (ℝ^d)) : Prop :=
  (⋃ t ∈ T, t +ᵥ P) = Set.univ ∧
    T.Pairwise fun t₁ t₂ => Disjoint (interior (t₁ +ᵥ P)) (interior (t₂ +ᵥ P))

/-- The (closed) **Voronoi cell** of the site `p` with respect to a set of sites `S ⊆ ℝ^d`: the
set of points of `ℝ^d` whose Euclidean distance to `p` does not exceed their distance to any site
in `S`. The Voronoi cells `voronoiCell S p`, `p ∈ S`, form the **Voronoi diagram** of `S`. -/
def voronoiCell (S : Set (ℝ^d)) (p : ℝ^d) : Set (ℝ^d) :=
  {x | ∀ q ∈ S, dist x p ≤ dist x q}

/--
**Voronoi's conjecture.** Does every higher-dimensional tiling by translations of convex polytope
tiles have an affine transformation taking it to a Voronoi diagram?

Precisely: let $d \ge 0$, let $P \subseteq \mathbb{R}^d$ be a convex polytope with nonempty
interior, and let $T \subseteq \mathbb{R}^d$ be a set of translation vectors such that the
translates $t + P$, $t \in T$, tile $\mathbb{R}^d$ (so $P$ is a *parallelohedron*). Do there exist
an affine bijection $A$ of $\mathbb{R}^d$ and a lattice $L \subseteq \mathbb{R}^d$ such that $A(P)$
is the Dirichlet–Voronoi cell of the origin in $L$ for the Euclidean metric? Equivalently, does
some affine transformation $A$ take a tiling of $\mathbb{R}^d$ by translates of $P$ (the lattice
tiling $\{A^{-1}(p + A(P)) : p \in L\}$) to the Voronoi diagram of a lattice $L$?

Here a lattice is a discrete additive subgroup of $\mathbb{R}^d$ that spans $\mathbb{R}^d$. The
hypothesis that $P$ has nonempty interior excludes degenerate lower-dimensional polytopes, whose
translates could otherwise cover $\mathbb{R}^d$ with trivially disjoint (empty) interiors.

The conjecture is known to hold for $d \le 5$ and is open for $d \ge 6$.
-/
theorem voronoi_diagram :
    ∀ (d : ℕ) (P T : Set (ℝ^d)), IsConvexPolytope P → (interior P).Nonempty →
      IsTilingByTranslates P T →
        ∃ (A : ℝ^d ≃ᵃ[ℝ] ℝ^d) (L : Submodule ℤ (ℝ^d)) (_ : DiscreteTopology L)
          (_ : IsZLattice ℝ L), A '' P = voronoiCell L 0 := by
  sorry

end VoronoiDiagram

theorem VoronoiDiagram.voronoi_diagram.disproof : ¬ (type_of% @VoronoiDiagram.voronoi_diagram) := sorry
