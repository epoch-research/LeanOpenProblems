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
# Tuza's conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Tuza%27s_conjecture)
* [Tu90] Tuza, Zs. (1990). "A conjecture on triangles of graphs." *Graphs Combin.* 6,
  pp. 373--380.
* [Ha99] Haxell, P. E. (1999). "Packing and covering triangles in graphs." *Discrete Math.*
  195, pp. 251--254.
-/

namespace TuzaConjecture

variable {V : Type*}

/-- `C` is a **triangle cover** of `G`: a set of edges of `G` meeting every triangle of `G`.
Removing the edges of `C` from `G` leaves a triangle-free graph. -/
def IsTriangleCover (G : SimpleGraph V) (C : Set (Sym2 V)) : Prop :=
  C ⊆ G.edgeSet ∧ ∀ t : Finset V, G.IsNClique 3 t → ∃ e ∈ C, ∀ x ∈ e, x ∈ t

/-- `T` is a **triangle packing** of `G`: a set of pairwise edge-disjoint triangles of `G`.
Two distinct triangles are edge-disjoint exactly when they share at most one vertex. -/
def IsTrianglePacking (G : SimpleGraph V) (T : Set (Finset V)) : Prop :=
  (∀ t ∈ T, G.IsNClique 3 t) ∧
    ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → ((t₁ : Set V) ∩ (t₂ : Set V)).ncard ≤ 1

/-- The **triangle covering number** `τ(G)`: the least number of edges meeting every triangle
of `G`. -/
noncomputable def triangleCoverNumber (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ C : Set (Sym2 V), IsTriangleCover G C ∧ C.ncard = n}

/-- The **triangle packing number** `ν(G)`: the greatest number of pairwise edge-disjoint
triangles of `G`. -/
noncomputable def trianglePackingNumber (G : SimpleGraph V) : ℕ :=
  sSup {n | ∃ T : Set (Finset V), IsTrianglePacking G T ∧ T.ncard = n}

/--
Tuza's conjecture (1981): every finite graph $G$ satisfies $\tau(G) \le 2\nu(G)$,
where $\tau(G)$ is its triangle covering number and $\nu(G)$ is its triangle packing number.
The bound would be sharp, for example for $K_4$ and $K_5$.
-/
theorem tuza_conjecture {V : Type} [Fintype V] (G : SimpleGraph V) :
    triangleCoverNumber G ≤ 2 * trianglePackingNumber G := by
  sorry

end TuzaConjecture

theorem TuzaConjecture.tuza_conjecture.disproof : ¬ (type_of% @TuzaConjecture.tuza_conjecture) := sorry
