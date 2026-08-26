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
# Conjectures associated with A100474

$a(1) = 1$; $a(n)$ is the smallest integer such that $a(n) + a(n-1)$ has the first $n$ distinct
prime factors not used before in this construction.

*References:*
- [A100474](https://oeis.org/A100474)
-/

namespace OeisA100474

/-- The $n$-th triangular number. -/
def triangular (n : ℕ) : ℕ := n * (n + 1) / 2

/-- The primary defining sequence `a`. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    (Finset.Ico (triangular (n + 1) - 1) (triangular (n + 2) - 1)).prod (Nat.nth Nat.Prime) -
      a (n + 1)

/--
After $a(2) = 5$, is there another prime?
-/
theorem conjecture : ∃ n > 2, (a n).Prime := by
  sorry

end OeisA100474
