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
# Erdős Problem 184

*References:*
- [erdosproblems.com/184](https://www.erdosproblems.com/184)
- [BM22] Bucić, M. and Montgomery, R., Towards the Erdős-Gallai Cycle Decomposition Conjecture.
  arXiv:2211.07689 (2022).
- [CFS14] Conlon, David and Fox, Jacob and Sudakov, Benny, Cycle packing. Random Structures
  Algorithms (2014), 608-626.
- [EGP66] Erdős, Paul and Goodman, A. W. and Pósa, Lajos, The representation of a graph by set
  intersections. Canadian J. Math. (1966), 106-112.
- [Er71] Erdős, P., Some unsolved problems in graph theory and combinatorial analysis. Combinatorial
  Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
-/

open Filter SimpleGraph

namespace Erdos184

/--
A graph $H$ is a cycle or an edge if it is connected and 2-regular, or if it has exactly one edge.
-/
def IsCycleOrEdge {U : Type*} [Fintype U] (H : SimpleGraph U) : Prop :=
  open scoped Classical in
  (H.Connected ∧ H.IsRegularOfDegree 2) ∨ H.edgeFinset.card = 1

/-- D is a decomposition of G into subgraphs. -/
def IsDecomposition {V : Type*} (G : SimpleGraph V) (D : Finset G.Subgraph) : Prop :=
  Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet) ∧
  (⋃ H ∈ D, H.edgeSet) = G.edgeSet

open scoped Classical in
/--
Conlon, Fox, and Sudakov [CFS14] proved that $O_\epsilon(n)$ cycles and edges suffice if $G$ has
minimum degree at least $\epsilon n$, for any $\epsilon>0$.
-/
theorem erdos_184.variants.conlon_fox_sudakov :
    ∀ ε > 0, ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (G.minDegree : ℝ) ≥ ε * (Fintype.card V : ℝ) →
      ∃ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  sorry

end Erdos184
