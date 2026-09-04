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
# Grünbaum–Nash-Williams conjecture

The Grünbaum–Nash-Williams conjecture asks whether every $4$-vertex-connected toroidal graph
has a Hamiltonian cycle. It generalises Tutte's theorem that every $4$-vertex-connected planar
graph has a Hamiltonian cycle.

A graph is *toroidal* if it can be drawn on the torus without crossings. Mathlib has no notion
of a graph embedded in a surface, so this file defines `EmbedsIn G X`: the vertices of `G` are
represented by distinct points of the topological space `X` and the edges by simple arcs, such
that arcs meet only at common endpoints and pass through no other vertex. This is the standard
topological definition of an embedding (see e.g. Mohar–Thomassen, *Graphs on Surfaces*, §2.1).
The torus is the product $\mathbb{R}/\mathbb{Z} \times \mathbb{R}/\mathbb{Z}$ of two circles.

*References:*
- [Wikipedia, Grünbaum–Nash-Williams conjecture](https://en.wikipedia.org/wiki/Gr%C3%BCnbaum%E2%80%93Nash-Williams_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Toroidal graph](https://en.wikipedia.org/wiki/Toroidal_graph)
- [Tu56] Tutte, W. T., *A theorem on planar graphs*, Trans. Amer. Math. Soc. 82 (1956), 99–116.
- [MT01] Mohar, B. and Thomassen, C., *Graphs on Surfaces*, Johns Hopkins University Press
  (2001).
-/

namespace GrunbaumNashWilliamsConjecture

open SimpleGraph
open scoped EuclideanGeometry

/-- The torus $\mathbb{T}^2 = S^1 \times S^1$, realised as the product of two copies of the
circle $\mathbb{R}/\mathbb{Z}$. -/
abbrev Torus : Type := UnitAddCircle × UnitAddCircle

/-- A simple graph `G` *embeds* in a topological space `X` if there are
* an injective map `f` sending vertices to points of `X`, and
* for each edge `e`, a simple arc `γ e` in `X` (a continuous injective map from $[0,1]$)
  whose endpoints are the images of the two endpoints of `e`,

such that an arc passes through the image of a vertex only at its own endpoints, and two
distinct arcs meet only at images of vertices (hence only at common endpoints). -/
def EmbedsIn {V : Type*} (G : SimpleGraph V) (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ (f : V → X) (γ : G.edgeSet → C(unitInterval, X)),
    Function.Injective f ∧
    (∀ e, Function.Injective (γ e)) ∧
    (∀ e : G.edgeSet, Sym2.map f e = s(γ e 0, γ e 1)) ∧
    (∀ (e : G.edgeSet) (v : V), f v ∈ Set.range (γ e) → v ∈ (e : Sym2 V)) ∧
    (∀ e e' : G.edgeSet, e ≠ e' → Set.range (γ e) ∩ Set.range (γ e') ⊆ Set.range f)

/-- A graph is *toroidal* if it embeds in the torus. Every planar graph is toroidal, see
`IsPlanar.isToroidal`. -/
def IsToroidal {V : Type*} (G : SimpleGraph V) : Prop :=
  EmbedsIn G Torus

/-- A graph is *planar* if it embeds in the Euclidean plane $\mathbb{R}^2$. -/
def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  EmbedsIn G ℝ²

/-- If `G` embeds in `X` then so does every subgraph of `G` on the same vertex set. -/
@[category API, AMS 5]
theorem EmbedsIn.anti {V : Type*} {G H : SimpleGraph V} {X : Type*} [TopologicalSpace X]
    (hHG : H ≤ G) (hG : EmbedsIn G X) : EmbedsIn H X := by
  obtain ⟨f, γ, hf, hγ, hends, hvert, hdisj⟩ := hG
  refine ⟨f, fun e => γ ⟨e, edgeSet_mono hHG e.2⟩, hf, fun e => hγ _,
    fun e => hends ⟨e, edgeSet_mono hHG e.2⟩,
    fun e v hv => hvert _ v hv, fun e e' hee' => hdisj _ _ fun h => hee' ?_⟩
  exact Subtype.ext congr(($h).1)

/-- An embedding in `X` composed with a continuous injection `X → Y` is an embedding in `Y`. -/
@[category API, AMS 5]
theorem EmbedsIn.of_injective_continuous {V : Type*} {G : SimpleGraph V}
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (hG : EmbedsIn G X)
    {φ : X → Y} (hφ : Function.Injective φ) (hφc : Continuous φ) : EmbedsIn G Y := by
  obtain ⟨f, γ, hf, hγ, hends, hvert, hdisj⟩ := hG
  refine ⟨φ ∘ f, fun e => (⟨φ, hφc⟩ : C(X, Y)).comp (γ e), hφ.comp hf,
    fun e => hφ.comp (hγ e), fun e => ?_, fun e v ⟨t, ht⟩ => hvert e v ⟨t, hφ ht⟩,
    fun e e' hee' y ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩ => ?_⟩
  · rw [← Sym2.map_map, hends e, Sym2.map_pair_eq]
    rfl
  · obtain ⟨v, hv⟩ := hdisj e e' hee' ⟨⟨t, hφ (ht.trans ht'.symm)⟩, ⟨t', rfl⟩⟩
    exact ⟨v, (congrArg φ hv).trans ht'⟩

/-- Every planar graph is toroidal: the plane embeds in the torus. -/
@[category API, AMS 5]
theorem IsPlanar.isToroidal {V : Type*} {G : SimpleGraph V} (hG : IsPlanar G) : IsToroidal G := by
  -- `g` is a continuous injection `ℝ → (0, 1)`, and `(↑)` is injective on `[0, 1)`.
  let g : ℝ → ℝ := fun x => 1 / 2 + Real.arctan x / Real.pi
  have hg : ∀ x, g x ∈ Set.Ico (0 : ℝ) (0 + 1) := fun x => by
    have h1 := Real.arctan_lt_pi_div_two x
    have h2 := Real.neg_pi_div_two_lt_arctan x
    have hpi := Real.pi_pos
    simp only [g, Set.mem_Ico, zero_add]
    constructor
    · have : -(1 / 2 : ℝ) < Real.arctan x / Real.pi := by
        rw [lt_div_iff₀ hpi]; linarith
      linarith
    · have : Real.arctan x / Real.pi < 1 / 2 := by
        rw [div_lt_iff₀ hpi]; linarith
      linarith
  have hginj : Function.Injective g := fun x y hxy => by
    simpa [g, Real.pi_ne_zero] using hxy
  have hgc : Continuous g := by fun_prop
  let φ : ℝ² → Torus := fun p => ((g (p 0) : UnitAddCircle), (g (p 1) : UnitAddCircle))
  refine hG.of_injective_continuous (φ := φ) (fun p q hpq => ?_) (by fun_prop)
  simp only [φ, Prod.mk.injEq, AddCircle.coe_eq_coe_iff_of_mem_Ico (hg _) (hg _)] at hpq
  ext i
  fin_cases i
  · exact hginj hpq.1
  · exact hginj hpq.2

/-- A single edge is planar: the definition of `EmbedsIn` is satisfiable. -/
@[category test, AMS 5]
theorem isPlanar_top_fin_two : IsPlanar (⊤ : SimpleGraph (Fin 2)) := by
  let p : ℝ² := EuclideanSpace.single 0 1
  have hp : p ≠ 0 := by
    simp [p]
  have hedge : ∀ e : (⊤ : SimpleGraph (Fin 2)).edgeSet, (e : Sym2 (Fin 2)) = s(0, 1) := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b =>
      rw [mem_edgeSet, top_adj] at he
      fin_cases a <;> fin_cases b <;> simp_all [Sym2.eq_swap]
  refine ⟨fun i => ((i : ℕ) : ℝ) • p, fun _ => ⟨fun t => (t : ℝ) • p, by fun_prop⟩,
    fun i j hij => ?_, fun e s t hst => ?_, fun e => ?_, fun e v _ => ?_, fun e e' hee' => ?_⟩
  · exact Fin.val_injective (Nat.cast_injective (smul_left_injective ℝ hp hij))
  · exact Subtype.val_injective (smul_left_injective ℝ hp hst)
  · rw [hedge e, Sym2.map_pair_eq]
    simp
  · rw [hedge e]
    fin_cases v <;> simp
  · exact absurd (Subtype.ext ((hedge e).trans (hedge e').symm)) hee'

/-- A single edge is toroidal. -/
@[category test, AMS 5]
theorem isToroidal_top_fin_two : IsToroidal (⊤ : SimpleGraph (Fin 2)) :=
  isPlanar_top_fin_two.isToroidal

/--
**Grünbaum–Nash-Williams conjecture.**
Does every $4$-vertex-connected toroidal graph have a Hamiltonian cycle?

Here a finite simple graph is $4$-vertex-connected if it has more than $4$ vertices and remains
connected after the removal of any set of fewer than $4$ vertices (`IsKConnected G 4`); this
excludes the degenerate graphs on at most $4$ vertices. It is toroidal if it can be drawn on the
torus without crossings (`IsToroidal`); planar graphs are included. The conjectured answer is yes.
-/
@[category research open, AMS 5]
theorem grunbaum_nash_williams_conjecture :
    answer(sorry) ↔ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsKConnected G 4 → IsToroidal G → G.IsHamiltonian := by
  sorry

end GrunbaumNashWilliamsConjecture
