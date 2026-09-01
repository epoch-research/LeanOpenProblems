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
Conjecture: $a(n) > 0$ for all $n > 1$.-/
theorem conjecture1 (n : ℕ) (hn : 1 < n) : 0 < a n := by
  sorry

end OeisA69004

theorem OeisA69004.conjecture1.disproof : ¬ (type_of% @OeisA69004.conjecture1) := sorry
