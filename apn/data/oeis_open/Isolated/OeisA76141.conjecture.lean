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
# Number of times $n$ occurs as a binary sub-pattern of $n^2$

The sequence $a(n)$ is the number of times the binary expansion of $n$ appears as a contiguous
sublist (infix) in the binary expansion of $n^2$.

*References:*
- [A076141](https://oeis.org/A076141)-/

namespace OeisA76141

/-- The binary representation of a natural number $n$, most significant bit first.
For $n = 0$, this is $[0]$. -/
def binaryPattern (n : ℕ) : List ℕ :=
  if n = 0 then [0] else (Nat.digits 2 n).reverse

/-- Number of times the binary pattern of $n$ occurs as an infix of the binary pattern of $n^2$. -/
def a (n : ℕ) : ℕ :=
  let pat := binaryPattern n
  let tgt := binaryPattern (n ^ 2)
  tgt.tails.countP (pat.isPrefixOf ·)

/--
Is $a(n) \le 1$ for all $n$?-/
theorem conjecture (n : ℕ) : a n ≤ 1 := by
  sorry

end OeisA76141

theorem OeisA76141.conjecture.disproof : ¬ (type_of% @OeisA76141.conjecture) := sorry
