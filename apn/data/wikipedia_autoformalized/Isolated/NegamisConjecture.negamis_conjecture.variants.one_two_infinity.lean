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
# Negami's conjecture

A *planar cover* of a finite graph $H$ is a finite planar graph $C$ together with a covering
map $f \colon C \to H$: a map from the vertices of $C$ onto the vertices of $H$ that, for every
vertex $v$ of $C$, restricts to a bijection between the neighbours of $v$ and the neighbours of
$f(v)$.

Every graph that embeds in the projective plane has a planar cover (its preimage in the sphere,
the orientable double cover of the projective plane). Negami conjectured the converse: every
connected graph with a planar cover embeds in the projective plane. Two equivalent
reformulations are also stated: the "$1$-$2$-$\infty$ conjecture" (a graph with a planar cover
has one of ply $1$ or $2$) and the statement that $K_{1,2,2,2}$ has no planar cover.

Mathlib has no notion of a planar or projective-planar graph, nor of a covering map of graphs.
We define drawings of a simple graph in an arbitrary topological space and specialise to the
plane $\mathbb{R}^2$ and to the real projective plane $\mathbb{R}P^2$, modelled as the quotient
of the unit sphere in $\mathbb{R}^3$ by the antipodal map.

*References:*
- [Wikipedia, *Planar cover*](https://en.wikipedia.org/wiki/Negami%27s_conjecture)
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Ne88] S. Negami, *The spherical genus and virtually planar graphs*,
  Discrete Math. 70 (1988), 159–168.
  [doi:10.1016/0012-365X(88)90090-8](https://doi.org/10.1016/0012-365X(88)90090-8)
- [Hl10] P. Hliněný, *20 years of Negami's planar cover conjecture*,
  Graphs Combin. 26 (2010), 525–536.
  [doi:10.1007/s00373-010-0934-9](https://doi.org/10.1007/s00373-010-0934-9)
- [RY10] Y. Rieck, Y. Yamashita, *Finite planar emulators for $K_{4,5} - 4K_2$ and $K_{1,2,2,2}$
  and Fellows' conjecture*, European J. Combin. 31 (2010), 903–907.
  [arXiv:0812.3700](https://arxiv.org/abs/0812.3700)
-/

namespace NegamisConjecture

open SimpleGraph unitInterval

variable {V W : Type*}

/-
## Topological embeddings of graphs
-/

/-- A drawing (topological embedding) of the simple graph `G` in the topological space `X`:
distinct vertices go to distinct points of `X`; every edge `uv` is drawn as an arc (an injective
path) from the point of `u` to the point of `v`, the arc of `vu` being the reverse of the arc of
`uv`; no arc passes through the point of a vertex except at its endpoints; and the arcs of two
different edges meet only at common endpoints. -/
structure Drawing (G : SimpleGraph V) (X : Type*) [TopologicalSpace X] where
  /-- The point of `X` representing a vertex. -/
  vertex : V → X
  vertex_injective : Function.Injective vertex
  /-- The arc representing an edge, oriented from `u` to `v`. -/
  edge ⦃u v : V⦄ : G.Adj u v → Path (vertex u) (vertex v)
  edge_symm ⦃u v : V⦄ (h : G.Adj u v) : edge h.symm = (edge h).symm
  edge_injective ⦃u v : V⦄ (h : G.Adj u v) : Function.Injective (edge h)
  edge_ne_vertex ⦃u v : V⦄ (h : G.Adj u v) (w : V) ⦃t : I⦄ :
    t ≠ 0 → t ≠ 1 → edge h t ≠ vertex w
  edge_disjoint ⦃u v u' v' : V⦄ (h : G.Adj u v) (h' : G.Adj u' v') ⦃s t : I⦄ :
    s ≠ 0 → s ≠ 1 → edge h s = edge h' t → s(u, v) = s(u', v')

/-- The simple graph `G` embeds in the topological space `X`. -/
def EmbedsIn (G : SimpleGraph V) (X : Type*) [TopologicalSpace X] : Prop :=
  Nonempty (Drawing G X)

/-- A simple graph is *planar* if it embeds in the plane $\mathbb{R}^2$. -/
def Planar (G : SimpleGraph V) : Prop :=
  EmbedsIn G (EuclideanSpace ℝ (Fin 2))

/-- The identification of antipodal points on the unit sphere of $\mathbb{R}^3$. -/
def antipodalSetoid : Setoid (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) where
  r x y := x = y ∨ x = -y
  iseqv := by
    refine ⟨fun _ => .inl rfl, fun h => ?_, fun h₁ h₂ => ?_⟩
    · rcases h with rfl | rfl <;> simp
    · rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp

/-- The real projective plane $\mathbb{R}P^2$: the unit sphere in $\mathbb{R}^3$ with antipodal
points identified, carrying the quotient topology. -/
abbrev RealProjectivePlane : Type :=
  Quotient antipodalSetoid

/-- A simple graph is *projective-planar* if it embeds in the projective plane
$\mathbb{R}P^2$. -/
def ProjectivePlanar (G : SimpleGraph V) : Prop :=
  EmbedsIn G RealProjectivePlane

/-
## Covering maps and planar covers
-/

/-- `f` is a *covering map* from the simple graph `C` onto the simple graph `H`: `f` maps the
vertices of `C` onto the vertices of `H` and, for every vertex `v` of `C`, restricts to a
bijection from the neighbours of `v` in `C` onto the neighbours of `f v` in `H`. -/
structure IsGraphCoveringMap (C : SimpleGraph V) (H : SimpleGraph W) (f : V → W) : Prop where
  surjective : Function.Surjective f
  bijOn (v : V) : Set.BijOn f (C.neighborSet v) (H.neighborSet (f v))

/-- The graph `H` has a *planar cover*: a finite planar graph `C` together with a covering map
from `C` onto `H`. -/
def HasPlanarCover (H : SimpleGraph W) : Prop :=
  ∃ (V : Type) (C : SimpleGraph V) (f : V → W),
    Finite V ∧ Planar C ∧ IsGraphCoveringMap C H f

/-- The graph `H` has a planar cover of *ply* `k` (a `k`-fold planar cover): a finite planar
graph `C` together with a covering map from `C` onto `H` under which every vertex of `H` has
exactly `k` preimages. -/
def HasPlanarCoverOfPly (H : SimpleGraph W) (k : ℕ) : Prop :=
  ∃ (V : Type) (C : SimpleGraph V) (f : V → W),
    Finite V ∧ Planar C ∧ IsGraphCoveringMap C H f ∧ ∀ w, Nat.card (f ⁻¹' {w}) = k

/-- The complete $4$-partite graph $K_{1,2,2,2}$ on $7$ vertices, with parts of sizes $1$, $2$,
$2$, $2$: two vertices are adjacent if and only if they lie in different parts. -/
abbrev K1222 : SimpleGraph (Σ i : Fin 4, Fin (![1, 2, 2, 2] i)) :=
  completeMultipartiteGraph fun i => Fin (![1, 2, 2, 2] i)

/-
## The conjecture
-/

/-- **Negami's "$1$-$2$-$\infty$ conjecture"**, a reformulation of Negami's conjecture: the
minimum ply of a planar cover of a finite graph, if it has one, is either $1$ or $2$. That is,
every finite graph with a planar cover has a planar cover of ply $1$ or a planar cover of
ply $2$.

The equivalence with `negamis_conjecture` uses Negami's theorem that a connected graph with a
$2$-fold planar cover is projective-planar, the sphere as the double cover of the projective
plane, and the fact that $2$-fold planar covers are closed under disjoint unions (so no
connectedness hypothesis is needed here). -/
theorem negamis_conjecture.variants.one_two_infinity [Finite W] (H : SimpleGraph W)
    (hcover : HasPlanarCover H) :
    HasPlanarCoverOfPly H 1 ∨ HasPlanarCoverOfPly H 2 := by
  sorry

end NegamisConjecture

theorem NegamisConjecture.negamis_conjecture.variants.one_two_infinity.disproof : ¬ (type_of% @NegamisConjecture.negamis_conjecture.variants.one_two_infinity) := sorry
