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

/--
**Grünbaum–Nash-Williams conjecture.**
Does every $4$-vertex-connected toroidal graph have a Hamiltonian cycle?

Here a finite simple graph is $4$-vertex-connected if it has more than $4$ vertices and remains
connected after the removal of any set of fewer than $4$ vertices (`IsKConnected G 4`); this
excludes the degenerate graphs on at most $4$ vertices. It is toroidal if it can be drawn on the
torus without crossings (`IsToroidal`); planar graphs are included. The conjectured answer is yes.
-/
theorem grunbaum_nash_williams_conjecture :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsKConnected G 4 → IsToroidal G → G.IsHamiltonian := by
  sorry

end GrunbaumNashWilliamsConjecture

theorem GrunbaumNashWilliamsConjecture.grunbaum_nash_williams_conjecture.disproof : ¬ (type_of% @GrunbaumNashWilliamsConjecture.grunbaum_nash_williams_conjecture) := sorry
