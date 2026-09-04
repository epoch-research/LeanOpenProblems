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
# Erdős–Ulam problem

The Erdős–Ulam problem asks whether the Euclidean plane contains a dense set of points
whose pairwise Euclidean distances are all rational numbers. The question was asked by
Ulam in 1946; Ulam and Erdős conjectured that no such set exists. The problem is open.
Tao and Shaffaf observed that the Bombieri–Lang conjecture implies a negative answer, and
Pasten showed that the abc conjecture also implies a negative answer.

The same problem appears as Erdős Problem 212, formalized in
`FormalConjectures.ErdosProblems.«212»` with the plane modeled as `ℂ`.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Ulam_problem)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [erdosproblems.com/212](https://www.erdosproblems.com/212)
- [Sh18] Shaffaf, J., *A solution of the Erdős–Ulam problem on rational distance sets assuming
  the Bombieri–Lang conjecture*. Discrete Comput. Geom. 60 (2018), 283–293.
  [arXiv:1501.00159](https://arxiv.org/abs/1501.00159)
- [SdZ10] Solymosi, J. and de Zeeuw, F., *On a question of Erdős and Ulam*.
  Discrete Comput. Geom. 43 (2010), 393–401. [arXiv:0806.3095](https://arxiv.org/abs/0806.3095)
-/

namespace ErdosUlamProblem

open EuclideanGeometry

/--
**Erdős–Ulam problem.** Is there a set $S \subseteq \mathbb{R}^2$ that is dense in the
Euclidean plane and such that the Euclidean distance between any two points of $S$ is a
rational number?

Here "dense" means topologically dense in the whole plane $\mathbb{R}^2$, and the distance
condition is required for every pair of points of $S$ (it holds trivially for a point and
itself, since the distance is $0$).
-/
@[category research open, AMS 11 52]
theorem erdos_ulam_problem :
    answer(sorry) ↔
      ∃ S : Set ℝ², Dense S ∧ ∀ p ∈ S, ∀ q ∈ S, ¬ Irrational (dist p q) := by
  sorry

end ErdosUlamProblem
