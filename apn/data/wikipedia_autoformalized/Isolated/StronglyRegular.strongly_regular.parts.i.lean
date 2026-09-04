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
# Strongly regular geodetic graphs

Do there exist infinitely many strongly regular geodetic graphs, or any strongly regular
geodetic graphs that are not Moore graphs?

A strongly regular graph $\operatorname{srg}(v, k, \lambda, \mu)$ is a $k$-regular graph on $v$
vertices in which every two adjacent vertices have $\lambda$ common neighbours and every two
distinct non-adjacent vertices have $\mu$ common neighbours (`SimpleGraph.IsSRGWith`). By
convention, the graphs which satisfy this definition trivially (disjoint unions of equal-sized
complete graphs, and complete multipartite graphs with equal-sized parts) are excluded.

A graph is *geodetic* if every two vertices are joined by a unique shortest path. Every strongly
regular graph with $\mu = 1$ is geodetic. Conversely, a non-trivial strongly regular graph is
connected of diameter $2$, and two non-adjacent vertices are joined by exactly $\mu$ shortest
paths, so it is geodetic only when $\mu = 1$. Hence the strongly regular geodetic graphs are
exactly the non-trivial strongly regular graphs with $\mu = 1$. Among graphs satisfying
`IsSRGWith n k ℓ 1`, the trivial ones are exactly the complete graphs `⊤` (including the graphs
on at most one vertex), for which the value of $\mu$ is vacuous: a disjoint union of at least two
cliques has $\mu = 0$, and a complete multipartite graph with at least two parts of size at least
two has $\mu \geq 2$. So non-triviality is expressed by `G ≠ ⊤`. Such a graph is automatically
connected.

The only known strongly regular graphs with $\mu = 1$ are the Moore graphs of diameter $2$, i.e.
the strongly regular graphs with $\lambda = 0$ and $\mu = 1$ (girth $5$): the pentagon, the
Petersen graph, the Hoffman–Singleton graph, and possibly a $57$-regular graph on $3250$
vertices. Parameters such as $(400, 21, 2, 1)$ have not been ruled out. It is known that
$\lambda = 1$ is impossible.

*References:*
- [Wikipedia, *Strongly regular graph*](https://en.wikipedia.org/wiki/Strongly_regular_graph)
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, *Geodetic graph*](https://en.wikipedia.org/wiki/Geodetic_graph)
- [Wikipedia, *Moore graph*](https://en.wikipedia.org/wiki/Moore_graph)
-/

namespace StronglyRegular

open SimpleGraph

open scoped Classical in
/--
Do there exist infinitely many strongly regular geodetic graphs?

Formalised as: is the set of orders $n$ for which there is a non-complete strongly regular graph
$\operatorname{srg}(n, k, \lambda, 1)$ infinite? Since there are only finitely many graphs on a
fixed number of vertices, this holds if and only if there are infinitely many pairwise
non-isomorphic such graphs. The complete graphs are excluded by `G ≠ ⊤`: they satisfy
`IsSRGWith` for every value of $\mu$, and they are the only trivial strongly regular graphs with
$\mu = 1$.
-/
theorem strongly_regular.parts.i : 
    {n : ℕ | ∃ (G : SimpleGraph (Fin n)) (k ℓ : ℕ),
      G.IsSRGWith n k ℓ 1 ∧ G ≠ ⊤}.Infinite := by
  sorry

end StronglyRegular

theorem StronglyRegular.strongly_regular.parts.i.disproof : ¬ (type_of% @StronglyRegular.strongly_regular.parts.i) := sorry
