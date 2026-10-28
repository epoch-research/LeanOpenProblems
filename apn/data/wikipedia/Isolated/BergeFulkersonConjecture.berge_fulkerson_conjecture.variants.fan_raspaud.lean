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
# The Berge–Fulkerson conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Petersen%27s_theorem#Related_conjectures)
* [Fu71] Fulkerson, D. R. (1971). "Blocking and anti-blocking pairs of polyhedra."
  *Math. Programming* 1, pp. 168--194.
* [Se79] Seymour, P. D. (1979). "On multi-colourings of cubic graphs, and conjectures of
  Fulkerson and Tutte." *Proc. London Math. Soc.* 38, pp. 423--460.
* [Ma11] Mazzuoccolo, G. (2011). "The equivalence of two conjectures of Berge and Fulkerson."
  *J. Graph Theory* 68, pp. 125--128.
* [FR94] Fan, G. and Raspaud, A. (1994). "Fulkerson's conjecture and circuit covers."
  *J. Combin. Theory Ser. B* 61, pp. 133--138.
* [Pe91] Petersen, J. (1891). "Die Theorie der regulären graphs." *Acta Math.* 15,
  pp. 193--220.
-/

open SimpleGraph Finset

namespace BergeFulkersonConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph is **cubic** if every vertex has degree `3`. -/
def IsCubic (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v, G.degree v = 3

open Classical in
/-- A family of `k` perfect matchings of `G` **covers every edge exactly `m` times** if each
member is a perfect matching and every edge of `G` lies in exactly `m` of them. -/
def IsPerfectMatchingCover (G : SimpleGraph V) (k m : ℕ) (M : Fin k → G.Subgraph) : Prop :=
  (∀ i, (M i).IsPerfectMatching) ∧
    ∀ e ∈ G.edgeSet, (univ.filter fun i => e ∈ (M i).edgeSet).card = m

/--
**The Fan–Raspaud conjecture (1994).**

Every bridgeless cubic graph has three perfect matchings with no edge common to all three.
This would follow from the Berge–Fulkerson conjecture.

*Reference:* [FR94].
-/
theorem berge_fulkerson_conjecture.variants.fan_raspaud :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      IsCubic G → G.IsBridgeless →
      ∃ M : Fin 3 → G.Subgraph, (∀ i, (M i).IsPerfectMatching) ∧
        ∀ e, ¬ (e ∈ (M 0).edgeSet ∧ e ∈ (M 1).edgeSet ∧ e ∈ (M 2).edgeSet) := by
  sorry

end BergeFulkersonConjecture

theorem BergeFulkersonConjecture.berge_fulkerson_conjecture.variants.fan_raspaud.disproof : ¬ (type_of% @BergeFulkersonConjecture.berge_fulkerson_conjecture.variants.fan_raspaud) := sorry
