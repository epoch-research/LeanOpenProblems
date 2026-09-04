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
# Total coloring conjecture

A *total coloring* of a graph $G$ assigns a color to every vertex and every edge of $G$ so that
adjacent vertices, adjacent edges, and an edge and either of its endpoints never receive the same
color. The *total chromatic number* $\chi''(G)$ is the least number of colors in a total coloring
of $G$; equivalently, it is the chromatic number of the *total graph* $T(G)$, whose vertices are
the vertices and edges of $G$, two of them being adjacent when the corresponding elements of $G$
are adjacent or incident.

The total coloring conjecture of Behzad and Vizing states that every finite simple graph $G$
satisfies $\chi''(G) \leq \Delta(G) + 2$, where $\Delta(G)$ is the maximum degree of $G$.

*References:*
- [Wikipedia, Total coloring](https://en.wikipedia.org/wiki/total_coloring_conjecture)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
-/

namespace TotalColoringConjecture

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/--
The total graph $T(G)$ of a simple graph `G`. Its vertices are the vertices of `G` (`Sum.inl v`)
together with the edges of `G` (`Sum.inr e`). Two vertices of `G` are adjacent in $T(G)$ if they are
adjacent in `G`; two edges of `G` are adjacent in $T(G)$ if they are distinct and share an endpoint
(that is, they are adjacent in the line graph of `G`); a vertex and an edge of `G` are adjacent in
$T(G)$ if the vertex is an endpoint of the edge.
-/
def totalGraph : SimpleGraph (V ⊕ G.edgeSet) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inl v, .inr e => v ∈ (e : Sym2 V)
    | .inr e, .inl v => v ∈ (e : Sym2 V)
    | .inr e, .inr f => G.lineGraph.Adj e f
  symm := by
    rintro (u | e) (v | f) h
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    rintro (v | e) h
    · exact G.loopless v h
    · exact G.lineGraph.loopless e h

/--
The total chromatic number $\chi''(G)$ of a simple graph `G`: the least number of colors in a
(proper) total coloring of `G`, that is, the chromatic number of the total graph of `G`.
-/
noncomputable def totalChromaticNumber : ℕ∞ := (totalGraph G).chromaticNumber

@[simp, category API, AMS 5]
theorem totalGraph_adj_inl_inl {u v : V} :
    (totalGraph G).Adj (Sum.inl u) (Sum.inl v) ↔ G.Adj u v :=
  Iff.rfl

@[simp, category API, AMS 5]
theorem totalGraph_adj_inl_inr {v : V} {e : G.edgeSet} :
    (totalGraph G).Adj (Sum.inl v) (Sum.inr e) ↔ v ∈ (e : Sym2 V) :=
  Iff.rfl

@[simp, category API, AMS 5]
theorem totalGraph_adj_inr_inl {v : V} {e : G.edgeSet} :
    (totalGraph G).Adj (Sum.inr e) (Sum.inl v) ↔ v ∈ (e : Sym2 V) :=
  Iff.rfl

@[simp, category API, AMS 5]
theorem totalGraph_adj_inr_inr {e f : G.edgeSet} :
    (totalGraph G).Adj (Sum.inr e) (Sum.inr f) ↔ G.lineGraph.Adj e f :=
  Iff.rfl

/-- The vertices of `G` induce a copy of `G` inside its total graph. -/
def totalGraphEmbeddingInl : G ↪g totalGraph G where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Iff.rfl

/-- The edges of `G` induce a copy of the line graph of `G` inside the total graph of `G`. -/
def totalGraphEmbeddingInr : G.lineGraph ↪g totalGraph G where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := Iff.rfl

/-- A total coloring of `G` restricts to a proper vertex coloring of `G`. -/
@[category API, AMS 5]
theorem chromaticNumber_le_totalChromaticNumber :
    G.chromaticNumber ≤ totalChromaticNumber G :=
  chromaticNumber_mono_of_hom (totalGraphEmbeddingInl G).toHom

/-- A total coloring of `G` restricts to a proper edge coloring of `G`. -/
@[category API, AMS 5]
theorem lineGraph_chromaticNumber_le_totalChromaticNumber :
    G.lineGraph.chromaticNumber ≤ totalChromaticNumber G :=
  chromaticNumber_mono_of_hom (totalGraphEmbeddingInr G).toHom

@[category test, AMS 5]
theorem totalGraph_bot : totalGraph (⊥ : SimpleGraph V) = ⊥ := by
  ext (u | e) (v | f)
  · simp
  · exact absurd f.property (by simp)
  · exact absurd e.property (by simp)
  · exact absurd e.property (by simp)

/-- The total graph of a single edge is a triangle. -/
@[category test, AMS 5]
theorem totalGraph_top_fin_two : totalGraph (⊤ : SimpleGraph (Fin 2)) = ⊤ := by
  have key : ∀ u a b : Fin 2, a ≠ b → u ∈ s(a, b) := by decide
  have uniq : ∀ a b c d : Fin 2, a ≠ b → c ≠ d → s(a, b) = s(c, d) := by decide
  ext (u | ⟨e, he⟩) (v | ⟨f, hf⟩)
  · simp
  · induction f using Sym2.ind with
    | h a b => simpa using key u a b (by simpa using hf)
  · induction e using Sym2.ind with
    | h a b => simpa using key v a b (by simpa using he)
  · induction e using Sym2.ind with
    | h a b =>
      induction f using Sym2.ind with
      | h c d =>
        have : (⟨s(a, b), he⟩ : (⊤ : SimpleGraph (Fin 2)).edgeSet) = ⟨s(c, d), hf⟩ :=
          Subtype.ext (uniq a b c d (by simpa using he) (by simpa using hf))
        rw [this]
        simp

/-- The total chromatic number of a single edge is $3 = \Delta + 2$. -/
@[category test, AMS 5]
theorem totalChromaticNumber_top_fin_two :
    totalChromaticNumber (⊤ : SimpleGraph (Fin 2)) = 3 := by
  rw [totalChromaticNumber, totalGraph_top_fin_two, chromaticNumber_top, Fintype.card_sum,
    ← edgeFinset_card, card_edgeFinset_top_eq_card_choose_two]
  norm_num

/--
The trivial lower bound: a vertex of maximum degree and the edges incident to it are pairwise
adjacent in the total graph, so $\Delta(G) + 1 \leq \chi''(G)$ for every finite graph $G$ with at
least one vertex.
-/
@[category textbook, AMS 5]
theorem maxDegree_add_one_le_totalChromaticNumber [Fintype V] [Nonempty V] [DecidableRel G.Adj] :
    G.maxDegree + 1 ≤ totalChromaticNumber G := by
  classical
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  let f : Option (G.incidenceSet v) → V ⊕ G.edgeSet := fun
    | none => Sum.inl v
    | some e => Sum.inr ⟨e, e.2.1⟩
  have hf : Pairwise fun i j ↦ (totalGraph G).Adj (f i) (f j) := by
    rintro (_ | e) (_ | e') h
    · exact absurd rfl h
    · exact e'.2.2
    · exact e.2.2
    · exact ⟨fun h' ↦ h (by simpa [Subtype.ext_iff] using h'), v, e.2.2, e'.2.2⟩
  have := le_chromaticNumber_of_pairwise_adj (n := G.degree v + 1) (by simp) f hf
  rw [hv]
  exact_mod_cast this

/--
**Total coloring conjecture** (Behzad, Vizing). For every finite simple graph $G$ the total
chromatic number is at most two plus the maximum degree: $\chi''(G) \leq \Delta(G) + 2$.
-/
@[category research open, AMS 5]
theorem total_coloring_conjecture [Fintype V] [DecidableRel G.Adj] :
    totalChromaticNumber G ≤ G.maxDegree + 2 := by
  sorry

end TotalColoringConjecture
