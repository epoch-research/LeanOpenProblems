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
# Albertson conjecture

The *Albertson conjecture* relates the crossing number of a graph to its chromatic number:
among all graphs with chromatic number $n$, the complete graph $K_n$ has the smallest crossing
number. Equivalently, every finite graph $G$ satisfies
$\operatorname{cr}(G) \ge \operatorname{cr}(K_{\chi(G)})$.

The *crossing number* $\operatorname{cr}(G)$ of a finite graph $G$ is the minimum number of edge
crossings over all drawings of $G$ in the plane. A drawing places the vertices at distinct points
and represents each edge by a simple arc between the images of its endpoints which does not pass
through the image of any vertex. A crossing is an unordered pair of distinct edges together with a
point of the plane lying in the interior of both of their arcs. The crossing number is not in
Mathlib, so it is defined here. No genericity conditions ("good drawing") are imposed on
drawings: a crossing-minimal drawing can always be chosen to be good, and every drawing has at
least as many crossings in the above sense as the classical crossing number, so the minimum is
unchanged.

*References:*
- [Wikipedia, Albertson conjecture](https://en.wikipedia.org/wiki/Albertson_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [ACF09] M. O. Albertson, D. W. Cranston, J. Fox, *Colorings, crossings, and cliques*,
  Electron. J. Combin. 16 (2009), R45. [arXiv:1006.3783](https://arxiv.org/abs/1006.3783)
- [BT10] J. Barát, G. Tóth, *Towards the Albertson conjecture*, Electron. J. Combin. 17 (2010),
  R73. [arXiv:0909.0413](https://arxiv.org/abs/0909.0413)
-/

open scoped EuclideanGeometry unitInterval

namespace AlbertsonConjecture

variable {V : Type*}

/-- A drawing of a simple graph `G` in the plane. The vertices are placed at distinct points,
and each edge is represented by a simple arc (a continuous injective map from the unit interval)
whose endpoints are the images of the two endpoints of the edge and whose interior does not pass
through the image of any vertex. -/
structure Drawing (G : SimpleGraph V) where
  /-- The point of the plane at which a vertex is placed. -/
  vertex : V → ℝ²
  vertex_injective : Function.Injective vertex
  /-- The arc representing an edge. -/
  arc : G.edgeSet → I → ℝ²
  arc_continuous (e : G.edgeSet) : Continuous (arc e)
  arc_injective (e : G.edgeSet) : Function.Injective (arc e)
  /-- The endpoints of the arc of an edge are the images of the endpoints of the edge. -/
  arc_endpoints (e : G.edgeSet) : Sym2.map vertex e = s(arc e 0, arc e 1)
  /-- The interior of an arc does not pass through the image of any vertex. -/
  arc_interior_not_mem_range (e : G.edgeSet) (t : I) (ht : t ∈ Set.Ioo 0 1) :
    arc e t ∉ Set.range vertex

variable {G : SimpleGraph V}

/-- The crossings of a drawing: an unordered pair of distinct edges together with a point of the
plane lying in the interior of both of their arcs. -/
def Drawing.crossings (D : Drawing G) : Set (Sym2 G.edgeSet × ℝ²) :=
  {c | ∃ e f : G.edgeSet, e ≠ f ∧ c.1 = s(e, f) ∧
    c.2 ∈ D.arc e '' Set.Ioo 0 1 ∧ c.2 ∈ D.arc f '' Set.Ioo 0 1}

/-- The crossing number of a graph: the minimum number of crossings over all of its drawings in
the plane. This is `⊤` if the graph has no drawing, which cannot happen for finite graphs. -/
noncomputable def crossingNumber (G : SimpleGraph V) : ℕ∞ :=
  ⨅ D : Drawing G, D.crossings.encard

/-- A drawing of a graph with no edges has no crossings. -/
@[category API, AMS 5]
theorem Drawing.crossings_bot (D : Drawing (⊥ : SimpleGraph V)) : D.crossings = ∅ := by
  ext ⟨p, x⟩
  simp only [Drawing.crossings, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨e, he⟩, -⟩
  simp at he

/-- A graph with no edges on a countable vertex set has crossing number zero. -/
@[category API, AMS 5]
theorem crossingNumber_bot [Countable V] : crossingNumber (⊥ : SimpleGraph V) = 0 := by
  obtain ⟨f, hf⟩ := exists_injective_nat V
  have hbot : ∀ e : (⊥ : SimpleGraph V).edgeSet, False := fun e => by simpa using e.2
  let D : Drawing (⊥ : SimpleGraph V) :=
    { vertex := fun v => EuclideanSpace.single 0 (f v : ℝ)
      vertex_injective := fun v w hvw => by
        have := congrArg (fun p : ℝ² => p 0) hvw
        simpa [EuclideanSpace.single_apply, hf.eq_iff] using this
      arc := fun e => (hbot e).elim
      arc_continuous := fun e => (hbot e).elim
      arc_injective := fun e => (hbot e).elim
      arc_endpoints := fun e => (hbot e).elim
      arc_interior_not_mem_range := fun e => (hbot e).elim }
  rw [crossingNumber, ENat.iInf_eq_zero]
  exact ⟨D, by rw [D.crossings_bot, Set.encard_empty]⟩

/-- The crossing number is monotone: a drawing of `G` restricts to a drawing of any subgraph
`H ≤ G` with no more crossings. -/
@[category API, AMS 5]
theorem crossingNumber_mono {H : SimpleGraph V} (hHG : H ≤ G) :
    crossingNumber H ≤ crossingNumber G := by
  let ι : H.edgeSet → G.edgeSet := fun e => ⟨e, SimpleGraph.edgeSet_mono hHG e.2⟩
  have hι : Function.Injective ι := fun e f h => Subtype.ext (congrArg Subtype.val h :)
  refine le_iInf fun D => ?_
  let D' : Drawing H :=
    { vertex := D.vertex
      vertex_injective := D.vertex_injective
      arc := fun e => D.arc (ι e)
      arc_continuous := fun e => D.arc_continuous (ι e)
      arc_injective := fun e => D.arc_injective (ι e)
      arc_endpoints := fun e => D.arc_endpoints (ι e)
      arc_interior_not_mem_range := fun e => D.arc_interior_not_mem_range (ι e) }
  refine (iInf_le _ D').trans ?_
  have hinj : Function.Injective (Prod.map (Sym2.map ι) (id : ℝ² → ℝ²)) :=
    (Sym2.map.injective hι).prodMap Function.injective_id
  rw [← hinj.encard_image]
  refine Set.encard_le_encard ?_
  rintro ⟨p, x⟩ ⟨⟨q, y⟩, ⟨e, f, hef, rfl, hx1, hx2⟩, h⟩
  simp only [Prod.map, id, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨ι e, ι f, fun h => hef (hι h), by simp, hx1, hx2⟩

/--
**Albertson conjecture**

Every finite simple graph $G$ has crossing number at least that of the complete graph with the
same chromatic number: if $\chi(G) = n$, then $\operatorname{cr}(G) \ge \operatorname{cr}(K_n)$.
Equivalently, among all graphs with chromatic number $n$, the complete graph $K_n$ has the
smallest crossing number.
-/
@[category research open, AMS 5]
theorem albertson_conjecture [Finite V] (G : SimpleGraph V) (n : ℕ)
    (hn : G.chromaticNumber = n) :
    crossingNumber (SimpleGraph.completeGraph (Fin n)) ≤ crossingNumber G := by
  sorry

end AlbertsonConjecture
