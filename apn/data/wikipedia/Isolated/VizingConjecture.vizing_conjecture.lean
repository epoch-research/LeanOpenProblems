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
# Vizing's conjecture (1968)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Vizing%27s_conjecture)
* [Vi68] Vizing, V. G. (1968). "Some unsolved problems in graph theory."
  *Uspekhi Mat. Nauk* 23, pp. 117--134.
* [ClSu00] Clark, W. E. and Suen, S. (2000). "An inequality related to Vizing's conjecture."
  *Electron. J. Combin.* 7, N4.
* [SuTa12] Suen, S. and Tarr, J. (2012). "An improved inequality related to Vizing's conjecture."
  *Electron. J. Combin.* 19, P8.
* [BDGHHKR12] Brešar, B., Dorbec, P., Goddard, W., Hartnell, B. L., Henning, M. A., Klavžar, S.
  and Rall, D. F. (2012). "Vizing's conjecture: a survey and recent results."
  *J. Graph Theory* 69, pp. 46--76.
-/

open SimpleGraph

namespace VizingConjecture

/--
**Vizing's conjecture (1968).**

For all finite simple graphs $G$ and $H$, the domination number of the Cartesian (box)
product satisfies $\gamma(G \,\square\, H) \ge \gamma(G)\,\gamma(H)$.
-/
theorem vizing_conjecture :
    ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      (G : SimpleGraph α) (H : SimpleGraph β),
      G.dominationNumber * H.dominationNumber ≤ (G □ H).dominationNumber := by
  sorry

end VizingConjecture

theorem VizingConjecture.vizing_conjecture.disproof : ¬ (type_of% @VizingConjecture.vizing_conjecture) := sorry
