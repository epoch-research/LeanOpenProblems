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
theorem lindelof_hypothesis (ε : ℝ) (hε : 0 < ε) :
    (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =o[atTop] fun t : ℝ => t ^ ε := by
  sorry

end LindelofHypothesis

theorem LindelofHypothesis.lindelof_hypothesis.disproof : ¬ (type_of% @LindelofHypothesis.lindelof_hypothesis) := sorry
