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
# Teschner's bondage number conjecture

The *bondage number* $b(G)$ of a nonempty finite simple graph $G$ (a graph with at least one
edge) is the minimum number of edges whose removal from $G$ strictly increases the domination
number $\gamma(G)$:
$$b(G) = \min\{|B| : B \subseteq E(G),\ \gamma(G - B) > \gamma(G)\}.$$

Fink, Jacobson, Kinch and Roberts (1990) conjectured that $b(G) \le \Delta(G) + 1$, where
$\Delta(G)$ is the maximum degree of $G$. Teschner disproved this with $K_3 \square K_3$, and
Hartnell–Rall and Teschner showed that
$b(K_n \square K_n) = 3(n-1) = \frac32 \Delta(K_n \square K_n)$ for $n \ge 3$.
Teschner (1995) then conjectured that $b(G) \le \frac{3}{2}\Delta(G)$ for every
graph $G$. This conjecture is open.

*References:*
- [Wikipedia, Bondage number](https://en.wikipedia.org/wiki/bondage_number)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Xu12] Jun-Ming Xu, *On Bondage Numbers of Graphs: A Survey with Some Comments*,
  [arXiv:1204.4010](https://arxiv.org/abs/1204.4010), Conjecture 3.6.3.
- [Tes95] Ulrich Teschner, *A new upper bound for the bondage number of graphs with small
  domination number*, Australas. J. Combin. 12 (1995), 27–35.
-/

namespace TeschnersBondageNumberConjecture

open SimpleGraph

variable {V : Type*}

/-- A finite set `B` of edges of `G` is a *bondage set* of `G` if removing the edges in `B`
from `G` strictly increases the domination number. -/
def IsBondageSet (G : SimpleGraph V) (B : Finset (Sym2 V)) : Prop :=
  ↑B ⊆ G.edgeSet ∧ G.dominationNumber < (G.deleteEdges ↑B).dominationNumber

/-- The *bondage number* `b(G)` of a graph `G` is the minimum size of a bondage set of `G`,
that is, the minimum number of edges whose removal strictly increases the domination number.

If `G` has no edges then no bondage set exists and, by the convention `sInf ∅ = 0`,
this returns `0`; the literature leaves `b(G)` undefined (or infinite) in that case. -/
noncomputable def bondageNumber (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ B : Finset (Sym2 V), IsBondageSet G B ∧ B.card = n}

/--
**Teschner's bondage number conjecture** (Teschner 1995; Conjecture 3.6.3 in [Xu12]).

Is the bondage number of a graph always less than or equal to $\frac{3}{2}$ times its maximum
degree? That is, does every finite simple graph $G$ with at least one edge satisfy
$$b(G) \le \tfrac{3}{2}\,\Delta(G)?$$

The graph is required to have at least one edge because the bondage number is only defined for
nonempty graphs. The bound is known to be sharp:
$b(K_n \square K_n) = \frac32 \Delta(K_n \square K_n)$ for $n \ge 3$.
-/
theorem teschners_bondage_number_conjecture :
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.edgeSet.Nonempty →
      (bondageNumber G : ℚ) ≤ 3 / 2 * G.maxDegree := by
  sorry

end TeschnersBondageNumberConjecture

theorem TeschnersBondageNumberConjecture.teschners_bondage_number_conjecture.disproof : ¬ (type_of% @TeschnersBondageNumberConjecture.teschners_bondage_number_conjecture) := sorry
