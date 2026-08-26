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
# Sidorenko's conjecture (1993)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Sidorenko%27s_conjecture)
* [Si93] Sidorenko, A. (1993). "A correlation inequality for bipartite graphs."
  *Graphs Combin.* 9, pp. 201--204.
* [CoFo10] Conlon, D. and Fox, J. (2010). "Bounds for graph regularity and removal lemmas."
  *Geom. Funct. Anal.* 22, pp. 1191--1256.
* [KLL18] Kim, J.H., Lee, C., Lee, J. (2018). "Two approaches to Sidorenko's conjecture."
  *Trans. Amer. Math. Soc.* 370, pp. 8515--8552.
* [ArXiv2605] [arXiv:2605.14138](https://arxiv.org/abs/2605.14138)
-/

open Finset SimpleGraph

namespace SidorenkoConjecture

open LimitObjects

/- ## Homomorphism density

We use `SimpleGraph.homCount` / `SimpleGraph.homDensity` from
`FormalConjecturesForMathlib.Combinatorics.SimpleGraph.HomDensity` for finite host graphs,
and `graphonHomDensity` / `graphonEdgeDensity` from
`FormalConjecturesForMathlib.Combinatorics.LimitObjects.Graphon` for graphons on measure spaces. -/

variable {V W : Type*}

/- ## The conjecture -/

/- ## Proved graphon special cases -/

/- ## Tournament Anti-Sidorenko (TAS) Trees Conjecture -/

open scoped Classical in
/--
**Tournament Anti-Sidorenko (TAS) Trees Conjecture.**

For every finite undirected tree $T$, there exists an orientation $\vec{T}$ of its edges such that
for any finite tournament $G$, the homomorphism density satisfies:
$$ t_{\vec{T}}(G) \le 2^{-e(T)} $$
where $e(T)$ is the total number of edges in $T$.
-/
theorem tournament_anti_sidorenko_trees_conjecture : 
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
      T.IsTree →
      ∃ (D : Digraph V),
        D.IsOrientation T ∧
        ∀ {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
          (G : Digraph W) [DecidableRel G.Adj],
          G.IsTournament →
          Digraph.homDensity D G ≤ (1 / 2 : ℝ) ^ T.edgeFinset.card := by
  sorry

open scoped Classical in
/--
**The $(2,3,4)$-spider tree.**
A tree composed of three paths of lengths 2, 3, and 4 joined at a single central vertex.
-/
def IsSpider234 {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj] : Prop :=
  T.IsTree ∧ Fintype.card V = 10 ∧
  ∃ (center l₁ l₂ l₃ : V),
    T.degree center = 3 ∧
    l₁ ≠ l₂ ∧ l₁ ≠ l₃ ∧ l₂ ≠ l₃ ∧
    T.degree l₁ = 1 ∧ T.degree l₂ = 1 ∧ T.degree l₃ = 1 ∧
    ({T.dist center l₁, T.dist center l₂, T.dist center l₃} : Multiset ℕ) = {2, 3, 4}

/- ## Proved special cases -/

/- ## Sidorenko for `K_{2,2}`: auxiliary lemmas -/

/- ## Sidorenko for trees: auxiliary lemmas -/

end SidorenkoConjecture
