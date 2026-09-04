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
# Zeeman conjecture

The Zeeman conjecture (Zeeman's collapsibility conjecture) asks whether, given a finite
contractible $2$-dimensional CW complex $K$, the space $K \times [0, 1]$ is collapsible.

Collapsibility is a piecewise linear notion, so $K$ is modelled by a finite simplicial complex
of dimension $2$ in some $\mathbb{R}^d$ (every finite $2$-dimensional polyhedron can be
triangulated in this way). "Collapsible" is meant in the piecewise linear sense: the polyhedron
$K \times [0, 1] \subseteq \mathbb{R}^d \times \mathbb{R}$ admits some triangulation that
collapses to a single vertex, i.e. it is PL homeomorphic to a collapsible simplicial complex.
It is important not to fix a cell structure on $K \times [0, 1]$: Adiprasito and Benedetti
showed that for every $m$ there is a finite contractible $2$-complex $K$ such that the $m$-th
derived subdivision of the product cell complex $K \times [0, 1]$ is not collapsible, while
$K \times [0, 1]$ is PL homeomorphic to a collapsible complex if and only if some iterated
derived subdivision of $K \times [0, 1]$ is collapsible.

The conjecture implies the Poincaré conjecture and the Andrews–Curtis conjecture.

*References:*
- [Wikipedia, Zeeman conjecture](https://en.wikipedia.org/wiki/Zeeman_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Ze64] Zeeman, E. C. "On the dunce hat." Topology 2 (1964): 341–358.
- [AB12] Adiprasito, K., Benedetti, B. "Subdivisions, shellability, and the Zeeman conjecture."
  [arXiv:1202.6606](https://arxiv.org/abs/1202.6606)
-/

namespace ZeemanConjecture

open Geometry

section Collapsibility

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The face `σ` of the simplicial complex `K` is a *free face* of `K` with coface `τ`: `τ` is
the only face of `K` that strictly contains `σ`. -/
def IsFreeFace (K : SimplicialComplex 𝕜 E) (σ τ : Finset E) : Prop :=
  σ ∈ K.faces ∧ τ ∈ K.faces ∧ σ ⊂ τ ∧ ∀ ρ ∈ K.faces, σ ⊂ ρ → ρ = τ

/-- The simplicial complex `L` is obtained from `K` by an *elementary collapse*: `L` is `K` with
a free face `σ` and its unique coface `τ` removed. -/
def ElementaryCollapse (K L : SimplicialComplex 𝕜 E) : Prop :=
  ∃ σ τ, IsFreeFace K σ τ ∧ L.faces = K.faces \ {σ, τ}

/-- The simplicial complex `K` *collapses* onto `L` if `L` is obtained from `K` by a finite
sequence of elementary collapses. -/
def Collapses (K L : SimplicialComplex 𝕜 E) : Prop :=
  Relation.ReflTransGen ElementaryCollapse K L

/-- A simplicial complex is *collapsible* if it collapses onto a single vertex. -/
def Collapsible (K : SimplicialComplex 𝕜 E) : Prop :=
  ∃ L, Collapses K L ∧ ∃ v, L.faces = {{v}}

/-- The coface `τ` of a free face is a facet. -/
@[category API, AMS 57]
theorem IsFreeFace.mem_facets {K : SimplicialComplex 𝕜 E} {σ τ : Finset E}
    (h : IsFreeFace K σ τ) : τ ∈ K.facets := by
  obtain ⟨-, hτ, hστ, huniq⟩ := h
  exact ⟨hτ, fun ρ hρ hτρ => (huniq ρ hρ (hστ.trans_subset hτρ)).symm⟩

/-- The coface `τ` of a free face `σ` has exactly one more vertex than `σ`. -/
@[category API, AMS 57]
theorem IsFreeFace.card_eq {K : SimplicialComplex 𝕜 E} {σ τ : Finset E}
    (h : IsFreeFace K σ τ) : τ.card = σ.card + 1 := by
  classical
  obtain ⟨-, hτ, hστ, huniq⟩ := h
  obtain ⟨x, hxτ, hxσ⟩ := Finset.exists_of_ssubset hστ
  have hρ : insert x σ ∈ K.faces :=
    K.down_closed hτ (Finset.insert_subset hxτ hστ.subset) (Finset.insert_nonempty x σ)
  rw [← huniq _ hρ (Finset.ssubset_insert hxσ), Finset.card_insert_of_notMem hxσ]

/-- An elementary collapse produces a subcomplex. -/
@[category API, AMS 57]
theorem ElementaryCollapse.le {K L : SimplicialComplex 𝕜 E} (h : ElementaryCollapse K L) :
    L ≤ K := by
  obtain ⟨σ, τ, -, hL⟩ := h
  show L.faces ⊆ K.faces
  rw [hL]
  exact Set.diff_subset

/-- A complex collapses only onto its subcomplexes. -/
@[category API, AMS 57]
theorem Collapses.le {K L : SimplicialComplex 𝕜 E} (h : Collapses K L) : L ≤ K := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact h.le.trans ih

/-- The empty complex is not collapsible. -/
@[category test, AMS 57]
theorem not_collapsible_bot : ¬ Collapsible (⊥ : SimplicialComplex 𝕜 E) := by
  rintro ⟨L, hL, v, hv⟩
  have : L.faces = ∅ := Set.subset_eq_empty hL.le (SimplicialComplex.faces_bot ..)
  simp [this] at hv

end Collapsibility

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A subset `P` of a real vector space is *collapsible in the PL sense* if it admits a finite
(linear) triangulation that is collapsible, i.e. there is a finite simplicial complex `T` whose
underlying space is `P` and which collapses to a vertex. Equivalently, the polyhedron `P` is PL
homeomorphic to a collapsible simplicial complex. -/
def IsPLCollapsible (P : Set E) : Prop :=
  ∃ T : SimplicialComplex ℝ E, T.faces.Finite ∧ T.space = P ∧ Collapsible T

/-- A single point is collapsible in the PL sense. -/
@[category test, AMS 57]
theorem isPLCollapsible_singleton (x : E) : IsPLCollapsible ({x} : Set E) := by
  refine ⟨⟨{{x}}, by simp, ?_, ?_, ?_⟩, Set.finite_singleton _, ?_, ⟨_, .refl, x, rfl⟩⟩
  · rintro s rfl
    exact affineIndependent_of_subsingleton ℝ _
  · rintro s t rfl hts ht
    rcases Finset.subset_singleton_iff.1 hts with rfl | rfl
    · exact absurd ht Finset.not_nonempty_empty
    · exact Set.mem_singleton _
  · rintro s t rfl rfl
    simp
  · simp [SimplicialComplex.space]

/--
**Zeeman conjecture.** Given a finite contractible two-dimensional CW complex $K$, is the space
$K \times [0, 1]$ collapsible?

Here $K$ is a finite contractible simplicial complex of dimension $2$ in some $\mathbb{R}^d$
(every finite $2$-dimensional polyhedron can be triangulated in this way), and "collapsible" is
meant in the PL sense: the polyhedron $K \times [0, 1] \subseteq \mathbb{R}^d \times \mathbb{R}$
admits a collapsible triangulation, i.e. it is PL homeomorphic to a collapsible complex.
-/
@[category research open, AMS 57]
theorem zeeman_conjecture :
    answer(sorry) ↔ ∀ (d : ℕ) (K : SimplicialComplex ℝ (Fin d → ℝ)), K.faces.Finite →
      (∀ s ∈ K.faces, s.card ≤ 3) → (∃ s ∈ K.faces, s.card = 3) → ContractibleSpace K.space →
      IsPLCollapsible (K.space ×ˢ Set.Icc (0 : ℝ) 1) := by
  sorry

end ZeemanConjecture
