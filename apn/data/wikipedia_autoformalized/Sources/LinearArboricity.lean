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

/-- The graph with no edges is a linear forest. -/
@[category test, AMS 5]
theorem isLinearForest_bot : IsLinearForest (⊥ : SimpleGraph V) :=
  ⟨isAcyclic_bot, iSup_le fun v => by simp [edegree, neighborSet]⟩

/-- The graph with no edges has linear arboricity `0`. -/
@[category test, AMS 5]
theorem linearArboricity_bot : linearArboricity (⊥ : SimpleGraph V) = 0 :=
  Nat.sInf_eq_zero.mpr <|
    Or.inl ⟨Fin.elim0, ⟨(iSup_of_empty _).symm, fun i => i.elim0⟩, fun i => i.elim0⟩

/-- A partition of the edges of `G` into `k` linear forests witnesses $\mathrm{la}(G) \leq k$. -/
@[category API, AMS 5]
theorem linearArboricity_le {G : SimpleGraph V} {k : ℕ} {c : Fin k → SimpleGraph V}
    (hc : G.IsEdgeColouring c) (hf : ∀ i, IsLinearForest (c i)) : linearArboricity G ≤ k :=
  Nat.sInf_le ⟨c, hc, hf⟩

/-- A single edge is a linear forest. -/
@[category test, AMS 5]
theorem isLinearForest_top_fin_two : IsLinearForest (⊤ : SimpleGraph (Fin 2)) := by
  refine ⟨?_, iSup_le fun v => ?_⟩
  · have : (⊤ : SimpleGraph (Fin 2)) = ⊥ ⊔ fromEdgeSet {s(0, 1)} := by
      ext a b; fin_cases a <;> fin_cases b <;> simp
    rw [this, isAcyclic_add_edge_iff_of_not_reachable 0 1 (by simp [reachable_bot])]
    exact isAcyclic_bot
  · calc ((⊤ : SimpleGraph (Fin 2)).neighborSet v).encard ≤ (Set.univ : Set (Fin 2)).encard :=
          Set.encard_le_encard (Set.subset_univ _)
      _ = 2 := by simp

/-- A single edge has linear arboricity `1`. -/
@[category test, AMS 5]
theorem linearArboricity_top_fin_two : linearArboricity (⊤ : SimpleGraph (Fin 2)) = 1 := by
  have hc : (⊤ : SimpleGraph (Fin 2)).IsEdgeColouring fun _ : Fin 1 => ⊤ :=
    ⟨iSup_const.symm, fun i j h => (h (Subsingleton.elim i j)).elim⟩
  refine le_antisymm (linearArboricity_le hc fun _ => isLinearForest_top_fin_two) ?_
  refine Nat.one_le_iff_ne_zero.mpr fun h => ?_
  rcases Nat.sInf_eq_zero.mp h with ⟨c, hc, -⟩ | h
  · exact top_ne_bot (hc.1.trans (iSup_of_empty c))
  · exact Set.notMem_empty 1 (h ▸ ⟨fun _ => ⊤, hc, fun _ => isLinearForest_top_fin_two⟩)

/--
**The linear arboricity conjecture** (Akiyama, Exoo and Harary, 1981). Every finite simple graph
$G$ with maximum degree $\Delta$ has linear arboricity
$$\mathrm{la}(G) \leq \left\lceil \frac{\Delta + 1}{2} \right\rceil,$$
that is, the edges of $G$ can be partitioned into $\lceil (\Delta + 1) / 2 \rceil$ linear forests
(disjoint unions of paths).

If $\Delta = 0$ then $G$ has no edges, $\mathrm{la}(G) = 0$, and the bound holds trivially.
-/
@[category research open, AMS 5]
theorem linear_arboricity [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    linearArboricity G ≤ ⌈(G.maxDegree + 1 : ℚ) / 2⌉₊ := by
  sorry

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
@[category research open, AMS 5]
theorem linear_arboricity.variants.regular [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {Δ : ℕ} (hΔ : 0 < Δ) (hG : G.IsRegularOfDegree Δ) :
    linearArboricity G = ⌈(Δ + 1 : ℚ) / 2⌉₊ := by
  sorry

end LinearArboricity
