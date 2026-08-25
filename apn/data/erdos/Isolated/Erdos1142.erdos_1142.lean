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

/-!
# Erdős Problem 1142

*References:*
- [erdosproblems.com/1142](https://www.erdosproblems.com/1142)
- [A039669](https://oeis.org/A039669)
- [Va99] Various, Some of Paul's favorite problems. Booklet produced for the conference "Paul Erdős
  and his mathematics", Budapest, July 1999 (1999).
- [MiWe69] Mientka, W. E. and Weitzenkamp, R. C., On f-plentiful numbers, Journal of
  Combinatorial Theory, Volume 7, Issue 4, December 1969, pages 374-377.

-/

open Nat Set

namespace Erdos1142

/--
The property that $n > 2$ and $n - 2^k$ is prime for all $k \geq 1$ with $2^k < n$.

Following the OEIS [A039669](https://oeis.org/A039669) convention ("Numbers n > 2 such that ..."),
we require $n > 2$ to exclude the trivial cases $n \leq 2$, for which the primality condition
is vacuously satisfied.
-/
def Erdos1142Prop (n : ℕ) : Prop :=
  2 < n ∧ ∀ k, 0 < k → 2 ^ k < n → (n - 2 ^ k).Prime

/--
Are there infinitely many $n > 2$ such that $n - 2^k$ is prime for all $k \geq 1$ with $2^k < n$?

The only known such $n$ are $4, 7, 15, 21, 45, 75, 105$ (OEIS [A039669](https://oeis.org/A039669)).
-/
theorem erdos_1142 :
    Infinite { n | Erdos1142Prop n } := by
  sorry

/-- Helper tactic for proving `Erdos1142Prop` for small concrete values. -/
local macro "prove_erdos_1142_prop" bound:num : tactic =>
  `(tactic| (
    refine ⟨by omega, fun k hk hlt => ?_⟩
    have : k ≤ $bound := by
      by_contra h; push_neg at h
      exact absurd (Nat.pow_le_pow_right (by omega : 1 ≤ 2) h) (by omega)
    interval_cases k <;> simp_all (config := { decide := true })))

end Erdos1142

theorem Erdos1142.erdos_1142.disproof : ¬ (type_of% @Erdos1142.erdos_1142) := sorry
