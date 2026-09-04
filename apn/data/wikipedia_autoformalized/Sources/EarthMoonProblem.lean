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
# Earth–Moon problem

The Earth–Moon problem, posed by Gerhard Ringel in 1959, asks for the maximum chromatic number
of a biplanar graph, i.e. of a finite simple graph whose edges can be partitioned into two
planar subgraphs (a graph of thickness at most two). It is known that this maximum is at least
$9$ (Sulanke, 1974: the join $K_6 + C_5$ needs $9$ colours) and at most $12$ (Ringel, 1959).
Ringel conjectured the answer $8$, which Sulanke's example refuted; Gethner conjectured in 2018
that the answer is $11$.

Mathlib has no notion of planar graph, so this file defines planarity directly: a graph is
planar if it has a drawing in the Euclidean plane with vertices as distinct points and edges as
simple arcs that meet only at common endpoints.

*References:*
- [Wikipedia, Earth–Moon problem](https://en.wikipedia.org/wiki/Earth%E2%80%93Moon_problem)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Open Problem Garden, Earth-Moon Problem](http://www.openproblemgarden.org/op/earth_moon_problem)
- [Ri59] Ringel, G., *Färbungsprobleme auf Flächen und Graphen*, VEB Deutscher Verlag der
  Wissenschaften, Berlin (1959).
- [Ge18] Gethner, E., *To the Moon and beyond*, in: Graph Theory: Favorite Conjectures and
  Open Problems, II, Springer (2018), 115–133.
  [doi:10.1007/978-3-319-97686-0_11](https://doi.org/10.1007/978-3-319-97686-0_11)
-/

open SimpleGraph
open scoped EuclideanGeometry unitInterval

namespace EarthMoonProblem

variable {V : Type*}

/-- A **planar drawing** of a simple graph `G`. The vertices are placed at distinct points of the
Euclidean plane $\mathbb{R}^2$. Every edge `e` is drawn as a simple arc `arc e`, a continuous
injective map from $[0,1]$ into $\mathbb{R}^2$, whose two end points are the points of the two
end vertices of `e`. An arc passes through a vertex point only at its end points, and two distinct
arcs meet only in vertex points (hence only in common end vertices). -/
structure PlanarDrawing (G : SimpleGraph V) where
  /-- The point of the plane at which a vertex is drawn. -/
  vertex : V → ℝ²
  vertex_injective : Function.Injective vertex
  /-- The simple arc along which an edge is drawn. -/
  arc : G.edgeSet → C(I, ℝ²)
  arc_injective : ∀ e, Function.Injective (arc e)
  /-- The end points of the arc of `e` are the points of the two end vertices of `e`. -/
  arc_ends : ∀ e : G.edgeSet, s(arc e 0, arc e 1) = (e : Sym2 V).map vertex
  /-- An arc meets a vertex point only at its own end points. -/
  arc_vertex : ∀ (e : G.edgeSet) (t : I), arc e t ∈ Set.range vertex → t = 0 ∨ t = 1
  /-- Two distinct arcs meet only in vertex points. -/
  arc_inter : ∀ e e' : G.edgeSet, e ≠ e' →
    Set.range (arc e) ∩ Set.range (arc e') ⊆ Set.range vertex

/-- A simple graph is **planar** if it has a planar drawing. -/
def IsPlanar (G : SimpleGraph V) : Prop :=
  Nonempty (PlanarDrawing G)

/-- A simple graph is **biplanar** (has thickness at most two) if its edge set can be partitioned
into two subsets such that the two corresponding spanning subgraphs are both planar. -/
def IsBiplanar (G : SimpleGraph V) : Prop :=
  ∃ G₁ G₂ : SimpleGraph V,
    Disjoint G₁ G₂ ∧ G₁ ⊔ G₂ = G ∧ IsPlanar G₁ ∧ IsPlanar G₂

/-- If the vertex type injects into the plane, the empty graph on it is planar: place the
vertices at the given points and draw no arcs. -/
@[category API, AMS 5]
theorem isPlanar_bot_of_injective (f : V → ℝ²) (hf : Function.Injective f) :
    IsPlanar (⊥ : SimpleGraph V) :=
  have : IsEmpty (⊥ : SimpleGraph V).edgeSet := by simp
  ⟨{ vertex := f
     vertex_injective := hf
     arc := isEmptyElim
     arc_injective := isEmptyElim
     arc_ends := isEmptyElim
     arc_vertex := isEmptyElim
     arc_inter := isEmptyElim }⟩

/-- Every planar graph is biplanar. -/
@[category API, AMS 5]
theorem IsPlanar.isBiplanar {G : SimpleGraph V} (hG : IsPlanar G) : IsBiplanar G :=
  have ⟨D⟩ := hG
  ⟨G, ⊥, disjoint_bot_right, sup_bot_eq G, hG,
    isPlanar_bot_of_injective D.vertex D.vertex_injective⟩

/-- The empty graph on finitely many vertices is planar. -/
@[category test, AMS 5]
theorem isPlanar_bot (n : ℕ) : IsPlanar (⊥ : SimpleGraph (Fin n)) :=
  isPlanar_bot_of_injective (fun i => !₂[(i : ℝ), 0]) fun i j h =>
    Fin.ext <| Nat.cast_injective (R := ℝ) <| by simpa [PiLp.ext_iff, Fin.forall_fin_two] using h

/-- The graph with a single edge is planar: draw the edge as a straight segment. -/
@[category test, AMS 5]
theorem isPlanar_top_fin_two : IsPlanar (⊤ : SimpleGraph (Fin 2)) := by
  have hEq : ∀ e ∈ (⊤ : SimpleGraph (Fin 2)).edgeSet, e = s(0, 1) := by
    intro e he
    induction e with | h a b =>
    simp only [mem_edgeSet, top_adj] at he
    fin_cases a <;> fin_cases b <;> simp_all [Sym2.eq_swap]
  let p : Fin 2 → ℝ² := fun i => EuclideanSpace.single 0 (i : ℝ)
  have hp : p 0 ≠ p 1 := by
    intro h
    have := congrArg (fun x : ℝ² => x 0) h
    simp [p] at this
  have hline : Function.Injective (AffineMap.lineMap (p 0) (p 1) : ℝ → ℝ²) :=
    AffineMap.lineMap_injective ℝ hp
  exact ⟨{ vertex := p
           vertex_injective := fun a b h => by
             fin_cases a <;> fin_cases b <;> simp_all
           arc := fun _ => ⟨fun t => AffineMap.lineMap (p 0) (p 1) (t : ℝ), by fun_prop⟩
           arc_injective := fun e s t hst => Subtype.ext (hline hst)
           arc_ends := fun e => by
             have := hEq e e.2
             simp [this]
           arc_vertex := fun e t ⟨w, hw⟩ => by
             fin_cases w
             · left
               refine Subtype.ext (hline ?_)
               simpa using hw.symm
             · right
               refine Subtype.ext (hline ?_)
               simpa using hw.symm
           arc_inter := fun e₁ e₂ h =>
             (h (Subtype.ext ((hEq _ e₁.2).trans (hEq _ e₂.2).symm))).elim }⟩

/-- **The Earth–Moon problem** (Ringel, 1959): what is the maximum chromatic number of biplanar
graphs? That is, determine the greatest value of the chromatic number $\chi(G)$ over all finite
simple biplanar graphs $G$. It is known that this maximum lies between $9$ and $12$, and
Gethner conjectures that it is $11$. -/
@[category research open, AMS 5]
theorem earth_moon_problem :
    IsGreatest
      {χ : ℕ | ∃ (n : ℕ) (G : SimpleGraph (Fin n)), IsBiplanar G ∧ G.chromaticNumber = χ}
      answer(sorry) := by
  sorry

end EarthMoonProblem
