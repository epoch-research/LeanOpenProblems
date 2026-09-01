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
**Conjecture 1.1 (Dean, 1988).** For every integer $k \geq 3$, every finite simple graph with
minimum degree at least $k$ contains a cycle whose length is divisible by $k$.

A cycle has length at least `3`, so the divisor is never `0` and the statement is not
satisfied for a trivial reason. `SimpleGraph.minDegree` is `0` on a graph with no vertices and
on a graph with no edges, so the hypothesis excludes both.
-/
theorem dean_conjecture :
    ∀ (k : ℕ), 3 ≤ k → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], k ≤ G.minDegree →
        ∃ m ∈ G.cycleLengths, k ∣ m := by
  sorry

end Arxiv.«2605.02731»

theorem Arxiv.«2605.02731».dean_conjecture.disproof : ¬ (type_of% @Arxiv.«2605.02731».dean_conjecture) := sorry
