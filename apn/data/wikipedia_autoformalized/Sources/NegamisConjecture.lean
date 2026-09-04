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

@[category test, AMS 57]
theorem realProjectivePlane_mk_neg (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (⟦-x⟧ : RealProjectivePlane) = ⟦x⟧ :=
  Quotient.sound (.inr rfl)

/-- The edgeless graph on a finite vertex type is planar. -/
@[category test, AMS 5 57]
theorem planar_bot (α : Type*) [Finite α] : Planar (⊥ : SimpleGraph α) := by
  let e := Finite.equivFin α
  let p : α → EuclideanSpace ℝ (Fin 2) := fun a => EuclideanSpace.single 0 ((e a : ℕ) : ℝ)
  have hp : Function.Injective p := fun a b hab => by
    have := congrFun (congrArg (⇑) hab) 0
    simp [p] at this
    exact e.injective (Fin.ext (by exact_mod_cast this))
  exact ⟨{ vertex := p
           vertex_injective := hp
           edge := fun _ _ h => h.elim
           edge_symm := fun _ _ h => h.elim
           edge_injective := fun _ _ h => h.elim
           edge_ne_vertex := fun _ _ h => h.elim
           edge_disjoint := fun _ _ _ _ h => h.elim }⟩

/-- The complete graph on two vertices is planar: draw its edge as a straight segment. -/
@[category test, AMS 5 57]
theorem planar_top_fin_two : Planar (⊤ : SimpleGraph (Fin 2)) := by
  let p : Fin 2 → EuclideanSpace ℝ (Fin 2) := fun i => EuclideanSpace.single 0 (i : ℝ)
  have hp : Function.Injective p := fun i j hij => by
    have := congrFun (congrArg (⇑) hij) 0
    simp [p] at this
    exact Fin.ext (by exact_mod_cast this)
  refine ⟨{ vertex := p
            vertex_injective := hp
            edge := fun u v _ => Path.segment (p u) (p v)
            edge_symm := fun u v _ => ?_
            edge_injective := fun u v h => ?_
            edge_ne_vertex := fun u v h w t ht0 ht1 => ?_
            edge_disjoint := fun u v u' v' h h' s t _ _ _ => ?_ }⟩
  · ext t
    simp [Path.symm, AffineMap.lineMap_apply_one_sub]
  · intro s t hst
    have := AffineMap.lineMap_injective ℝ (hp.ne h.ne) (by simpa using hst)
    exact Subtype.ext this
  · have huw : w = u ∨ w = v := by
      have := h.ne
      fin_cases u <;> fin_cases v <;> fin_cases w <;> simp_all
    rcases huw with rfl | rfl
    · simp [hp.ne h.ne, ht0]
    · simp [hp.ne h.ne, ht1]
  · have := h.ne
    have := h'.ne
    fin_cases u <;> fin_cases v <;> fin_cases u' <;> fin_cases v' <;> simp_all [Sym2.eq_swap]

@[category test, AMS 5 57]
theorem projectivePlanar_bot_unit : ProjectivePlanar (⊥ : SimpleGraph Unit) :=
  ⟨{ vertex := fun _ => ⟦⟨EuclideanSpace.single 0 1, by simp⟩⟧
     vertex_injective := fun _ _ _ => Subsingleton.elim _ _
     edge := fun _ _ h => h.elim
     edge_symm := fun _ _ h => h.elim
     edge_injective := fun _ _ h => h.elim
     edge_ne_vertex := fun _ _ h => h.elim
     edge_disjoint := fun _ _ _ _ h => h.elim }⟩

/-
## Covering maps and planar covers
-/

/-- `f` is a *covering map* from the simple graph `C` onto the simple graph `H`: `f` maps the
vertices of `C` onto the vertices of `H` and, for every vertex `v` of `C`, restricts to a
bijection from the neighbours of `v` in `C` onto the neighbours of `f v` in `H`. -/
structure IsGraphCoveringMap (C : SimpleGraph V) (H : SimpleGraph W) (f : V → W) : Prop where
  surjective : Function.Surjective f
  bijOn (v : V) : Set.BijOn f (C.neighborSet v) (H.neighborSet (f v))

/-- A covering map is a graph homomorphism. -/
@[category API, AMS 5]
theorem IsGraphCoveringMap.adj {C : SimpleGraph V} {H : SimpleGraph W} {f : V → W}
    (hf : IsGraphCoveringMap C H f) {u v : V} (huv : C.Adj u v) : H.Adj (f u) (f v) :=
  (hf.bijOn u).mapsTo huv

@[category test, AMS 5]
theorem isGraphCoveringMap_id (G : SimpleGraph V) : IsGraphCoveringMap G G id :=
  ⟨Function.surjective_id, fun _ => Set.bijOn_id _⟩

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

/-- A finite planar graph is a `1`-fold planar cover of itself. -/
@[category test, AMS 5 57]
theorem hasPlanarCoverOfPly_one_of_planar {α : Type} [Finite α] {G : SimpleGraph α}
    (hG : Planar G) : HasPlanarCoverOfPly G 1 := by
  refine ⟨α, G, id, ‹_›, hG, isGraphCoveringMap_id G, fun w => ?_⟩
  simp

/-- Two disjoint copies of a single vertex form a `2`-fold planar cover of a single vertex. -/
@[category test, AMS 5 57]
theorem hasPlanarCoverOfPly_bot_unit_two : HasPlanarCoverOfPly (⊥ : SimpleGraph Unit) 2 := by
  refine ⟨Fin 2, ⊥, fun _ => (), inferInstance, planar_bot (Fin 2),
    ⟨fun _ => ⟨0, rfl⟩, fun v => ?_⟩, fun w => ?_⟩
  · simp [SimpleGraph.neighborSet]
  · simp

/-- The complete $4$-partite graph $K_{1,2,2,2}$ on $7$ vertices, with parts of sizes $1$, $2$,
$2$, $2$: two vertices are adjacent if and only if they lie in different parts. -/
abbrev K1222 : SimpleGraph (Σ i : Fin 4, Fin (![1, 2, 2, 2] i)) :=
  completeMultipartiteGraph fun i => Fin (![1, 2, 2, 2] i)

@[category test, AMS 5]
theorem card_K1222 : Fintype.card (Σ i : Fin 4, Fin (![1, 2, 2, 2] i)) = 7 := by
  simp [Fintype.card_sigma, Fin.sum_univ_succ]

@[category test, AMS 5]
theorem card_edgeFinset_K1222 : K1222.edgeFinset.card = 18 := by
  decide

/-
## The conjecture
-/

/-- **Negami's conjecture** (Negami, 1988). Every connected finite graph that has a planar
cover embeds in the projective plane. Equivalently (the converse being a theorem), a connected
finite graph has a planar cover if and only if it embeds in the projective plane.

The connectedness hypothesis cannot be dropped: a disjoint union of projective-planar graphs
has a planar cover but need not be projective-planar. -/
@[category research open, AMS 5 57]
theorem negamis_conjecture [Finite W] (H : SimpleGraph W) (hH : H.Connected)
    (hcover : HasPlanarCover H) : ProjectivePlanar H := by
  sorry

/-- **Negami's "$1$-$2$-$\infty$ conjecture"**, a reformulation of Negami's conjecture: the
minimum ply of a planar cover of a finite graph, if it has one, is either $1$ or $2$. That is,
every finite graph with a planar cover has a planar cover of ply $1$ or a planar cover of
ply $2$.

The equivalence with `negamis_conjecture` uses Negami's theorem that a connected graph with a
$2$-fold planar cover is projective-planar, the sphere as the double cover of the projective
plane, and the fact that $2$-fold planar covers are closed under disjoint unions (so no
connectedness hypothesis is needed here). -/
@[category research open, AMS 5 57]
theorem negamis_conjecture.variants.one_two_infinity [Finite W] (H : SimpleGraph W)
    (hcover : HasPlanarCover H) :
    HasPlanarCoverOfPly H 1 ∨ HasPlanarCoverOfPly H 2 := by
  sorry

/-- The complete $4$-partite graph $K_{1,2,2,2}$ has no planar cover.

By work of Archdeacon, Fellows, Hliněný and Negami on the $32$ connected minor-minimal
non-projective-planar graphs, this statement is equivalent to Negami's conjecture: proving it
would complete a proof of the conjecture, and if the conjecture is false then $K_{1,2,2,2}$ is
its smallest counterexample. -/
@[category research open, AMS 5 57]
theorem negamis_conjecture.variants.K1222 : ¬ HasPlanarCover K1222 := by
  sorry

end NegamisConjecture
