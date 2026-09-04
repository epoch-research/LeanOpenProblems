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
# Conference graphs

A *conference graph* is a strongly regular graph with parameters
$(v, k, \lambda, \mu) = (v, (v - 1)/2, (v - 5)/4, (v - 1)/4)$. It is the graph associated with a
symmetric conference matrix of order $v + 1$, so its number of vertices $v$ must be
congruent to $1$ modulo $4$ and a sum of two squares. Conference graphs are known to exist for
all prime powers $v \equiv 1 \pmod 4$ (the Paley graphs), for $v = 45$ (Mathon, 1978) and for
$v = 65$ (Gritsenko, 2021). The smallest open case is $v = 85$.

*References:*
- [Wikipedia, Conference graph](https://en.wikipedia.org/wiki/conference_graph)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Ma78] R. Mathon, [*Symmetric Conference Matrices of Order $pq^2 + 1$*](https://doi.org/10.4153/CJM-1978-029-1),
  Canadian Journal of Mathematics, 1978.
- [BvM22] A. E. Brouwer, H. Van Maldeghem,
  [*Strongly regular graphs*](https://homepages.cwi.nl/~aeb/math/srg/rk3/srgw.pdf), 2022.
- [Gr21] O. Gritsenko, *On strongly regular graph with parameters (65, 32, 15, 16)*,
  [arXiv:2102.05432](https://arxiv.org/abs/2102.05432).
-/

namespace ConferenceGraph

open SimpleGraph

open scoped Classical in
/--
Does there exist a conference graph for every number of vertices $v > 1$ where
$v \equiv 1 \pmod 4$ and $v$ is an odd sum of two squares?

A conference graph on $v$ vertices is a strongly regular graph with parameters
$(v, (v - 1)/2, (v - 5)/4, (v - 1)/4)$. The condition $v \equiv 1 \pmod 4$ already forces $v$ to
be odd, and the restriction $v > 1$ excludes the degenerate one-vertex graph, which satisfies the
parameter conditions vacuously; hence $v \ge 5$ and all divisions in the parameters are exact.
-/
theorem conference_graph :
    
      ∀ v : ℕ, 1 < v → v ≡ 1 [MOD 4] → (∃ a b : ℕ, v = a ^ 2 + b ^ 2) →
        ∃ G : SimpleGraph (Fin v), G.IsSRGWith v ((v - 1) / 2) ((v - 5) / 4) ((v - 1) / 4) := by
  sorry

end ConferenceGraph

theorem ConferenceGraph.conference_graph.disproof : ¬ (type_of% @ConferenceGraph.conference_graph) := sorry
