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

import FormalConjectures.Util.ProblemImports

open Nat

/--
A386660: $a(n) = \sum_{k=1}^n \binom{n}{k} \pmod{2^k}$.
-/
def a (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sum fun k => (n.choose k) % (2 ^ k)

/--
oeis_386660_conjecture_0: The limit of $a(n)^{1/n}$ exists.
The numerical evidence suggests a limit of approximately $1.7086...$
-/
theorem oeis_386660_conjecture_0 :
  let f (n : ℕ) : ℝ := (a n : ℝ) ^ (1 / (n : ℝ))
  ∃ L : ℝ, Filter.Tendsto f Filter.atTop (nhds L) := by
  sorry
