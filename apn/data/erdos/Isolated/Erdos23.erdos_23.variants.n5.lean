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
# Erdős Problem 23

*References:*
* [erdosproblems.com/23](https://www.erdosproblems.com/23)
* [OEIS A389646](https://oeis.org/A389646)
* [Balogh-Clemen-Lidicky, Max Cuts in Triangle-free Graphs](https://arxiv.org/abs/2103.14179)
* [McKay, Extremal graphs for bipartization of triangle-free graphs](https://users.cecs.anu.edu.au/~bdm/data/graphs.html)
-/

open SimpleGraph BigOperators

namespace Erdos23

/--
Every triangle-free graph on $25$ vertices can be made bipartite by removing at most $25$
edges.

This is the $n = 5$ case of Erdős Problem 23.  It follows from the high-density range of
Balogh-Clemen-Lidicky together with McKay's complete catalogue of the 23-vertex extremal
graphs for bipartization of triangle-free graphs.
-/
theorem erdos_23.variants.n5 :
    ∀ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 25)),
        H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 25 := by
  sorry

/--
The blow-up of the 5-cycle $C_5$: replace each vertex of $C_5$ with an independent set of $n$
vertices, and connect two vertices iff their corresponding vertices in $C_5$ are adjacent.
The vertex set is $\mathbb{Z}/5\mathbb{Z} \times \{0, \ldots, n-1\}$, where $(i, a)$ and $(j, b)$
are adjacent iff $j = i + 1$ or $i = j + 1$ in $\mathbb{Z}/5\mathbb{Z}$.
-/
def blowupC5 (n : ℕ) : SimpleGraph (ZMod 5 × Fin n) :=
  SimpleGraph.fromRel fun (i, _) (j, _) => i + 1 = j ∨ j + 1 = i

-- TODO: add the remaining variants/statements/comments

end Erdos23
