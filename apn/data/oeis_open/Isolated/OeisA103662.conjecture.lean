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
# Smallest power with base>1 and exponent $n$ without digit 0

For statistical reasons it is conjectured that the sequence is finite.
Also it is conjectured that $a(40)$ does not exist (i.e. the sequence is empty for $n=40$).

*References:*
- [A103662](https://oeis.org/A103662)
-/

namespace OeisA103662

open Nat List Set

/--
A helper predicate: $b^n$ is a power with base $>1$ whose decimal representation
does not contain the digit 0.
We assume $n$ is the exponent, $n \ge 1$.
-/
def IsValidZerolessPower (n b : ℕ) : Prop :=
  b > 1 ∧ 0 ∉ digits 10 (b ^ n)

/--
The primary defining sequence `a`.
`a n` is the smallest power with base $>1$ and exponent $n$ whose decimal representation
doesn't contain the digit 0.
$$a(n) = (\min \{ b \in \mathbb{N} \mid b > 1,
  \text{decimal representation of } b^n \text{ contains no digit } 0 \})^n$$
If no such base exists, `sInf` of an empty set of naturals returns 0, so `a n = 0`.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let smallestBase := sInf { b | IsValidZerolessPower n b }
  smallestBase ^ n

/--
For statistical reasons it is conjectured that the sequence is finite.
This is formalized as the assertion that for large enough $n$, no valid zeroless power exists,
which in our definition results in $a(n) = 0$.
-/
theorem conjecture : ∃ N : ℕ, ∀ n : ℕ, n > N → a n = 0 := by
  sorry

end OeisA103662

theorem OeisA103662.conjecture.disproof : ¬ (type_of% @OeisA103662.conjecture) := sorry
