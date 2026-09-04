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
# The linear arboricity conjecture

A *linear forest* is an acyclic graph with maximum degree at most two, that is, a disjoint
union of paths. The *linear arboricity* $\mathrm{la}(G)$ of a graph $G$ is the smallest number
of linear forests into which its edges can be partitioned.

The linear arboricity conjecture of Akiyama, Exoo and Harary (1981) asserts that every graph
$G$ with maximum degree $\Delta$ satisfies
$$\mathrm{la}(G) \leq \left\lceil \frac{\Delta + 1}{2} \right\rceil.$$

*References:*
- [Wikipedia, Linear arboricity](https://en.wikipedia.org/wiki/linear_arboricity)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [AEH81] Akiyama, J., Exoo, G. and Harary, F., *Covering and packing in graphs. IV. Linear
  arboricity*. Networks 11 (1981), 69--72.
- [FFJ18] Ferber, A., Fox, J. and Jain, V., *Towards the linear arboricity conjecture*.
  [arXiv:1809.04716](https://arxiv.org/abs/1809.04716)
-/

open SimpleGraph

namespace LinearArboricity

variable {V : Type*}

/-- A graph `F` is a *linear forest* if it is acyclic and has maximum degree at most two.
Equivalently, `F` is a disjoint union of paths. The graph with no edges is a linear forest. -/
def IsLinearForest (F : SimpleGraph V) : Prop :=
  F.IsAcyclic ∧ F.emaxDegree ≤ 2

/-- The *linear arboricity* $\mathrm{la}(G)$ of a graph `G`: the least `k` such that the edges of
`G` can be partitioned into `k` linear forests. Here `c : Fin k → SimpleGraph V` is such a
partition when `G.IsEdgeColouring c`, that is, `G = ⨆ i, c i` and the `c i` are pairwise
edge-disjoint, and every `c i` is a linear forest. Some of the `c i` may have no edges, so this is
the least number of linear forests needed. For a finite graph such a partition always exists (one
edge per class), so the infimum is attained. -/
noncomputable def linearArboricity (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ c : Fin k → SimpleGraph V,
    G.IsEdgeColouring c ∧ ∀ i, IsLinearForest (c i)}

/--
**The linear arboricity conjecture for regular graphs.** For every $\Delta$-regular finite simple
graph $G$ with $\Delta \geq 1$,
$$\mathrm{la}(G) = \left\lceil \frac{\Delta + 1}{2} \right\rceil.$$

The lower bound $\mathrm{la}(G) \geq \lceil (\Delta + 1) / 2 \rceil$ is elementary for regular
graphs, so the open content is the upper bound. Since every graph of maximum degree $\Delta$
embeds in a $\Delta$-regular graph, this statement is equivalent to `linear_arboricity`
[FFJ18, Section 1].

The hypothesis $\Delta \geq 1$ excludes the edgeless regular graphs, which have linear arboricity
$0$. The hypothesis `Nonempty V` excludes the empty graph, which is vacuously $\Delta$-regular for
every $\Delta$ but has linear arboricity $0$.
-/
theorem linear_arboricity.variants.regular [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {Δ : ℕ} (hΔ : 0 < Δ) (hG : G.IsRegularOfDegree Δ) :
    linearArboricity G = ⌈(Δ + 1 : ℚ) / 2⌉₊ := by
  sorry

end LinearArboricity

theorem LinearArboricity.linear_arboricity.variants.regular.disproof : ¬ (type_of% @LinearArboricity.linear_arboricity.variants.regular) := sorry
