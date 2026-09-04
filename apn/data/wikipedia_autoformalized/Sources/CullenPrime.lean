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
# Cullen primes

A Cullen number is a number of the form $C_n = n \cdot 2^n + 1$, where $n$ is a natural
number. A Cullen prime is a Cullen number that is prime. Only sixteen Cullen primes are known,
namely $C_n$ for
$n = 1, 141, 4713, 5795, 6611, 18496, 32292, 32469, 59656, 90825, 262419, 361275, 481899,
1354828, 6328548, 6679881$.
It is conjectured that there are infinitely many Cullen primes.

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Cullen number](https://en.wikipedia.org/wiki/Cullen_number)
- [OEIS A005849](https://oeis.org/A005849)
-/

namespace CullenPrime

/--
Are there infinitely many Cullen primes? That is, are there infinitely many natural numbers
$n$ such that the Cullen number $C_n = n \cdot 2^n + 1$ is prime?

Since $n \mapsto n \cdot 2^n + 1$ is strictly increasing, this is equivalent to the set of
Cullen primes being infinite. The conjectured answer is yes.
-/
@[category research open, AMS 11]
theorem cullen_prime : answer(sorry) ↔ {n : ℕ | (n * 2 ^ n + 1).Prime}.Infinite := by
  sorry

end CullenPrime
