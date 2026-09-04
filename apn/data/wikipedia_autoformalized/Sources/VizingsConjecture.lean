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
# Vizing's conjecture

Vizing's conjecture (1968) relates the domination number $\gamma$ of the cartesian (box) product
$G \,\Box\, H$ of two finite simple graphs to the domination numbers of the factors. Here
$\gamma(G)$ is the minimum size of a dominating set of $G$, i.e. of a set $D$ of vertices such
that every vertex of $G$ is in $D$ or adjacent to a vertex of $D$.

The domination number is `SimpleGraph.dominationNumber` from
`FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination`, and the cartesian product
is Mathlib's `SimpleGraph.boxProd`, written `G □ H`.

*References:*
- [Wikipedia, Vizing's conjecture](https://en.wikipedia.org/wiki/Vizing%27s_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Vi68] Vizing, V. G. (1968). "Some unsolved problems in graph theory."
  *Uspekhi Mat. Nauk* 23 (6), pp. 117--134.
- [BDGHHKR12] Brešar, B., Dorbec, P., Goddard, W., Hartnell, B. L., Henning, M. A., Klavžar, S.,
  Rall, D. F. (2012). "Vizing's conjecture: a survey and recent results."
  *Journal of Graph Theory* 69 (1), pp. 46--76.
-/

namespace VizingsConjecture

open SimpleGraph

/--
**Vizing's conjecture** (Vizing, 1968). For all finite simple graphs $G$ and $H$,
$$\gamma(G \,\Box\, H) \ge \gamma(G)\,\gamma(H),$$
where $\gamma$ denotes the domination number (the minimum number of vertices in a dominating
set) and $G \,\Box\, H$ is the cartesian product of $G$ and $H$.

The graphs are finite, encoded by the `Finite` instances on the vertex types; no other
hypothesis is imposed. The domination number is a genuine minimum since the whole vertex set is
dominating. If one of the vertex types is empty then both sides are $0$ and the inequality holds
trivially, so the statement is equivalent to the usual one for graphs with nonempty vertex set.
-/
@[category research open, AMS 5]
theorem vizings_conjecture {α β : Type*} [Finite α] [Finite β]
    (G : SimpleGraph α) (H : SimpleGraph β) :
    G.dominationNumber * H.dominationNumber ≤ (G □ H).dominationNumber := by
  sorry

/-- The $4$-cycle $C_4$ has domination number $2$. -/
@[category test, AMS 5]
example : (cycleGraph 4).dominationNumber = 2 := by
  rw [dom_num_eq_computable]
  decide +native

/-- The product $C_4 \,\Box\, C_4$ (the $4$-dimensional hypercube) has domination number $4$,
so it meets the bound of Vizing's conjecture with equality. -/
@[category test, AMS 5]
example : (cycleGraph 4 □ cycleGraph 4).dominationNumber = 4 := by
  letI : DecidableRel (cycleGraph 4 □ cycleGraph 4).Adj := fun x y =>
    inferInstanceAs (Decidable ((cycleGraph 4).Adj x.1 y.1 ∧ x.2 = y.2 ∨
      (cycleGraph 4).Adj x.2 y.2 ∧ x.1 = y.1))
  rw [dom_num_eq_computable]
  decide +native

end VizingsConjecture
