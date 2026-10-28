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
# The total colouring conjecture (Behzad 1965, Vizing 1968)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Total_coloring)
* [Be65] Behzad, M. (1965). *Graphs and their chromatic numbers.* Ph.D. thesis, Michigan State
  University.
* [Vi68] Vizing, V. G. (1968). "Some unsolved problems in graph theory."
  *Uspekhi Mat. Nauk* 23, pp. 117--134.
* [Ko96] Kostochka, A. V. (1996). "The total chromatic number of any multigraph with maximum
  degree five is at most seven." *Discrete Math.* 162, pp. 199--214.
* [MR98] Molloy, M. and Reed, B. (1998). "A bound on the total chromatic number."
  *Combinatorica* 18, pp. 241--280.
* [Yap96] Yap, H. P. (1996). *Total colourings of graphs.* Lecture Notes in Mathematics 1623,
  Springer.
-/

open SimpleGraph

namespace TotalColoringConjecture

/--
**The total colouring conjecture (Behzad 1965, Vizing 1968).**

Every finite simple graph $G$ has a total colouring with at most $\Delta(G) + 2$ colours, i.e.
$\chi''(G) \le \Delta(G) + 2$, where $\Delta(G)$ is the maximum degree.
-/
theorem total_coloring_conjecture :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.totalChromaticNumber ≤ G.maxDegree + 2 := by
  sorry

end TotalColoringConjecture

theorem TotalColoringConjecture.total_coloring_conjecture.disproof : ¬ (type_of% @TotalColoringConjecture.total_coloring_conjecture) := sorry
