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
# The Petersen colouring conjecture (Jaeger 1988)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Petersen_graph#Petersen_coloring_conjecture)
* [Ja88] Jaeger, F. (1988). "Nowhere-zero flow problems." In *Selected Topics in Graph
  Theory 3*, Academic Press, pp. 71--95.
* [Mk13] Mkrtchyan, V. V. (2013). "A remark on the Petersen coloring conjecture of Jaeger."
  *Australas. J. Combin.* 56, pp. 145--151.
* [HS14] Hägglund, J. and Steffen, E. (2014). "Petersen-colorings and some families of
  snarks." *Ars Math. Contemp.* 7, pp. 161--173.
* [Zh97] Zhang, C.-Q. (1997). *Integer flows and cycle covers of graphs.* Marcel Dekker.
-/

open SimpleGraph Finset

namespace PetersenColoringConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A map `φ` on the edges of `G` into the edges of the Petersen graph `P` is a
**Petersen colouring** if for every vertex `v` of `G` there is a vertex `w` of `P` such that
`φ` maps the edges at `v` onto the edges at `w` (so in particular `φ` is a proper edge
colouring with the `15` edges of `P` as colours and every pair of adjacent edges goes to a pair
of adjacent edges). -/
def IsPetersenColoring (G : SimpleGraph V) [DecidableRel G.Adj]
    (φ : Sym2 V → Sym2 PetersenVertex) : Prop :=
  ∀ v : V, ∃ w : PetersenVertex,
    (G.incidenceFinset v).image φ = petersenGraph.incidenceFinset w ∧
      Set.InjOn φ (G.incidenceFinset v : Set (Sym2 V))

/--
**The Petersen colouring conjecture (Jaeger 1988).**

Every bridgeless cubic graph has a Petersen colouring: an edge colouring by the edges of the
Petersen graph such that the three edges at each vertex are mapped onto the three edges at
some vertex of the Petersen graph. Jaeger showed that this conjecture implies both the
Berge–Fulkerson conjecture and the cycle double cover conjecture.
-/
theorem petersen_coloring_conjecture :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v, G.degree v = 3) → G.IsBridgeless →
      ∃ φ : Sym2 V → Sym2 PetersenVertex, IsPetersenColoring G φ := by
  sorry

end PetersenColoringConjecture

theorem PetersenColoringConjecture.petersen_coloring_conjecture.disproof : ¬ (type_of% @PetersenColoringConjecture.petersen_coloring_conjecture) := sorry
