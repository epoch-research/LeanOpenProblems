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
# Lindelöf hypothesis

The Lindelöf hypothesis is a conjecture of Ernst Leonard Lindelöf about the rate of growth of
the Riemann zeta function $\zeta$ on the critical line $\operatorname{Re}(s) = 1/2$. It says
that for every $\varepsilon > 0$,
$$
  \zeta\left(\tfrac{1}{2} + it\right) = o(t^{\varepsilon}) \quad \text{as } t \to +\infty.
$$
Equivalently (since $\varepsilon$ can be replaced by a smaller value), for every
$\varepsilon > 0$ one has $\zeta(1/2 + it) = O(t^{\varepsilon})$ as $t \to +\infty$.
The hypothesis is implied by the Riemann hypothesis.

Here `riemannZeta` is Mathlib's analytic continuation of the Riemann zeta function to all
of $\mathbb{C}$, and $t$ ranges over the real numbers with $t \to +\infty$.

*References:*
- [Wikipedia: Lindelöf hypothesis](https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
-/

open Complex Filter Asymptotics

namespace LindelofHypothesis

/-- **Lindelöf hypothesis.** For all real $\varepsilon > 0$,
$$
  \zeta\left(\tfrac{1}{2} + it\right) = o(t^{\varepsilon})
$$
as the real variable $t$ tends to $+\infty$. -/
@[category research open, AMS 11]
theorem lindelof_hypothesis (ε : ℝ) (hε : 0 < ε) :
    (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =o[atTop] fun t : ℝ => t ^ ε := by
  sorry

/-- **Lindelöf hypothesis**, big-$O$ form. For all real $\varepsilon > 0$,
$$
  \zeta\left(\tfrac{1}{2} + it\right) = O(t^{\varepsilon})
$$
as the real variable $t$ tends to $+\infty$. This is equivalent to `lindelof_hypothesis`
since $\varepsilon$ can be replaced by a smaller value. -/
@[category research open, AMS 11]
theorem lindelof_hypothesis.variants.isBigO (ε : ℝ) (hε : 0 < ε) :
    (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[atTop] fun t : ℝ => t ^ ε := by
  sorry

/-- The little-$o$ and big-$O$ forms of the Lindelöf hypothesis are equivalent. -/
@[category test, AMS 11]
theorem lindelof_hypothesis_iff_isBigO :
    (∀ ε : ℝ, type_of% (lindelof_hypothesis ε)) ↔
      ∀ ε : ℝ, type_of% (lindelof_hypothesis.variants.isBigO ε) := by
  refine ⟨fun h ε hε => (h ε hε).isBigO, fun h ε hε => ?_⟩
  refine (h (ε / 2) (by positivity)).trans_isLittleO ?_
  refine isLittleO_of_tendsto' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with t ht h0
    exact absurd h0 (Real.rpow_pos_of_pos ht ε).ne'
  · refine (tendsto_rpow_neg_atTop (by positivity : 0 < ε / 2)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [← Real.rpow_sub ht]
    congr 1
    ring

end LindelofHypothesis
