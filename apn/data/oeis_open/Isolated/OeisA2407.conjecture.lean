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
# Cuban Primes

OEIS A002407 lists the primes that are differences of two consecutive positive cubes. The
sequence is conjectured to be infinite.

*References:*
- [OEIS A002407](https://oeis.org/A002407)
-/

namespace OeisA2407

/-- A natural number is in A002407 when it is prime and is the difference of two consecutive
positive cubes. The addition equality avoids truncated subtraction in `ℕ`. -/
def A (p : ℕ) : Prop :=
  p.Prime ∧ ∃ k > 0, p + k ^ 3 = (k + 1) ^ 3

/--
This sequence is believed to be infinite.
-/
theorem conjecture : {p : ℕ | A p}.Infinite := by
  sorry

end OeisA2407

theorem OeisA2407.conjecture.disproof : ¬ (type_of% @OeisA2407.conjecture) := sorry
