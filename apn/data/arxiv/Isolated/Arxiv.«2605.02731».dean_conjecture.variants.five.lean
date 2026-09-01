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
# Dean's conjecture on cycles of length divisible by `k`

*References:*
- [arxiv/2605.02731](https://arxiv.org/abs/2605.02731)
  **Existence of cycles of length divisible by 3 or 4**
  by *Ilkyoo Choi, Hojin Chu, Ringi Kim, Boram Park*, where this is Conjecture 1.1.
- [De88] Dean, N., Open problem, in Cycles and Rays. (1988).
- [DeLeSa93] Dean, N. and Lesniak, L. and Saito, A., Cycles of length 0 modulo 4 in graphs.
  Discrete Math. (1993), 133--139.
- [ChSa94] Chen, G. and Saito, A., Graphs with a cycle of length divisible by three.
  J. Combin. Theory Ser. B (1994), 277--292.
-/

open SimpleGraph

namespace Arxiv.«2605.02731»

/--
The case $k = 5$. This is the only case of the conjecture that is still open.
-/
theorem dean_conjecture.variants.five :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], 5 ≤ G.minDegree → ∃ m ∈ G.cycleLengths, 5 ∣ m := by
  sorry

end Arxiv.«2605.02731»

theorem Arxiv.«2605.02731».dean_conjecture.variants.five.disproof : ¬ (type_of% @Arxiv.«2605.02731».dean_conjecture.variants.five) := sorry
