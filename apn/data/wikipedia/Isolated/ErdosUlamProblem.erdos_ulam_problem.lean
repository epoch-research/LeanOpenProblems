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
# The Erdős–Ulam problem

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Ulam_problem)
* [Ul60] Ulam, S. M. (1960). *A Collection of Mathematical Problems.* Interscience, p. 40.
* [SdZ10] Solymosi, J. and de Zeeuw, F. (2010). "On a question of Erdős and Ulam."
  *Discrete Comput. Geom.* 43, pp. 393--401. [arXiv:0806.3095](https://arxiv.org/abs/0806.3095)
* [Ta14] Tao, T. (2014). "The Erdős–Ulam problem, varieties of general type, and the
  Bombieri–Lang conjecture." Blog post,
  [terrytao.wordpress.com](https://terrytao.wordpress.com/2014/12/20/the-erdos-ulam-problem-varieties-of-general-type-and-the-bombieri-lang-conjecture/)
* [AE45] Anning, N. H. and Erdős, P. (1945). "Integral distances." *Bull. Amer. Math. Soc.* 51,
  pp. 598--600.
-/

open EuclideanSpace

namespace ErdosUlamProblem

/-- A set of points of the plane has **pairwise rational distances** if the distance between any
two of its points is a rational number. -/
def PairwiseRationalDistances (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∃ r : ℚ, dist p q = (r : ℝ)

/--
**The Erdős–Ulam problem (Ulam 1945).**

Is there a dense subset of the plane whose points are at pairwise rational distances?
Conjecturally, no such set exists. Solymosi and de Zeeuw [SdZ10] proved that if a
rational-distance set has infinitely many points on a line or circle, all but finitely many
points lie on that line or circle.
-/
theorem erdos_ulam_problem :
    ∃ S : Set (EuclideanSpace ℝ (Fin 2)), Dense S ∧ PairwiseRationalDistances S := by
  sorry

end ErdosUlamProblem

theorem ErdosUlamProblem.erdos_ulam_problem.disproof : ¬ (type_of% @ErdosUlamProblem.erdos_ulam_problem) := sorry
