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
# Infinitude of Pell number primes

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Pell_number#Primes_and_squares)
 - [A86383](https://oeis.org/A86383)

The Pell numbers $P_n$ are defined by $P_0 = 0$,
$P_1 = 1$, $P_{n+2} = 2*P_{n+1} + P_n$. [OEIS A129](https://oeis.org/A129)

The conjecture says that there are infinitely many prime Pell numbers.
-/

namespace PellNumbers

/-- The *Pell numbers* $P_n$ are defined by $P_0 = 0$, $P_1 = 1$, $P_{n+2} = 2*P_{n+1} + P_n$ -/
def pellNumber : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 1 + 1 => 2 * pellNumber (n + 1) + pellNumber n

/-- There are infinitely many prime Pell numbers -/
theorem infinite_pellNumber_primes : Infinite {n : ℕ | Prime (pellNumber n)} := by
  sorry

-- TODO : Formalise connection between Pell numbers and Pell equation x^2 - 2*y^2 = -1

end PellNumbers

theorem PellNumbers.infinite_pellNumber_primes.disproof : ¬ (type_of% @PellNumbers.infinite_pellNumber_primes) := sorry
