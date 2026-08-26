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
# Number of times $n^2 + s^2$ is prime for positive integers $s < n$

The sequence $a(n)$ counts the number of integers $s \in \{1, \dots, n-1\}$ such that
$n^2 + s^2$ is prime:
$$a(n) = \sum_{s=1}^{n-1} [\text{Prime}(n^2 + s^2)]$$

*References:*
- [A069004](https://oeis.org/A069004)-/

namespace OeisA69004

open Finset

/-- Number of times $n^2 + s^2$ is prime for positive integers $s < n$. -/
def a (n : ℕ) : ℕ :=
  ∑ s ∈ Ico 1 n, if (n ^ 2 + s ^ 2).Prime then 1 else 0

/--
Stronger conjecture: Let $\pi(n)$ be the prime counting function (A000720).
Then $\pi(n) \ge a(n) \ge \pi(n)/5$ for $n > 1$, with the following equalities:
$\pi(2) = a(2)$, $\pi(10) = a(10)$ and $a(12) = \pi(12)/5$.-/
theorem conjecture2 :
    (∀ n : ℕ, 1 < n → Nat.primeCounting n ≥ a n) ∧
    (∀ n : ℕ, 1 < n → 5 * a n ≥ Nat.primeCounting n) ∧
    Nat.primeCounting 2 = a 2 ∧
    Nat.primeCounting 10 = a 10 ∧
    5 * a 12 = Nat.primeCounting 12 := by
  sorry

end OeisA69004
