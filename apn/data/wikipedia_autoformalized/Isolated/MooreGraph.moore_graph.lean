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
# Moore graph

A Moore graph is a regular graph whose girth is more than twice its diameter. A Moore graph of
diameter $k$ has girth $2k + 1$, so a Moore graph of girth $5$ has diameter $2$. Hoffman and
Singleton showed that a Moore graph of girth $5$ must have degree $2$, $3$, $7$ or $57$. The first
three cases are realised by the $5$-cycle, the Petersen graph and the Hoffman–Singleton graph. The
existence of a Moore graph of girth $5$ and degree $57$ is open. Such a graph would have
$1 + 57^2 = 3250$ vertices.

*References:*
* [Wikipedia, Moore graph](https://en.wikipedia.org/wiki/Moore_graph)
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [HS60] Hoffman, A. J. and Singleton, R. R. (1960). "On Moore graphs with diameters 2 and 3."
  *IBM Journal of Research and Development* 4 (5), pp. 497--504.
  [doi:10.1147/rd.45.0497](https://doi.org/10.1147/rd.45.0497)
-/

namespace MooreGraph

open SimpleGraph

/--
Does a Moore graph with girth $5$ and degree $57$ exist?

That is, is there a finite simple graph that is $57$-regular, has girth $5$ and has diameter $2$?
Any such graph is connected and has exactly $1 + 57^2 = 3250$ vertices. Note that
`SimpleGraph.girth` is `0` for an acyclic graph and `SimpleGraph.diam` is `0` for a disconnected
graph, so `G.girth = 5` and `G.diam = 2` force a genuine shortest cycle of length $5$ and a
connected graph of diameter $2$.
-/
theorem moore_graph :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      G.IsRegularOfDegree 57 ∧ G.girth = 5 ∧ G.diam = 2 := by
  sorry

end MooreGraph

theorem MooreGraph.moore_graph.disproof : ¬ (type_of% @MooreGraph.moore_graph) := sorry
