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

end Collapsibility

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A subset `P` of a real vector space is *collapsible in the PL sense* if it admits a finite
(linear) triangulation that is collapsible, i.e. there is a finite simplicial complex `T` whose
underlying space is `P` and which collapses to a vertex. Equivalently, the polyhedron `P` is PL
homeomorphic to a collapsible simplicial complex. -/
def IsPLCollapsible (P : Set E) : Prop :=
  ∃ T : SimplicialComplex ℝ E, T.faces.Finite ∧ T.space = P ∧ Collapsible T

/--
**Zeeman conjecture.** Given a finite contractible two-dimensional CW complex $K$, is the space
$K \times [0, 1]$ collapsible?

Here $K$ is a finite contractible simplicial complex of dimension $2$ in some $\mathbb{R}^d$
(every finite $2$-dimensional polyhedron can be triangulated in this way), and "collapsible" is
meant in the PL sense: the polyhedron $K \times [0, 1] \subseteq \mathbb{R}^d \times \mathbb{R}$
admits a collapsible triangulation, i.e. it is PL homeomorphic to a collapsible complex.
-/
theorem zeeman_conjecture :
    ∀ (d : ℕ) (K : SimplicialComplex ℝ (Fin d → ℝ)), K.faces.Finite →
      (∀ s ∈ K.faces, s.card ≤ 3) → (∃ s ∈ K.faces, s.card = 3) → ContractibleSpace K.space →
      IsPLCollapsible (K.space ×ˢ Set.Icc (0 : ℝ) 1) := by
  sorry

end ZeemanConjecture

theorem ZeemanConjecture.zeeman_conjecture.disproof : ¬ (type_of% @ZeemanConjecture.zeeman_conjecture) := sorry
