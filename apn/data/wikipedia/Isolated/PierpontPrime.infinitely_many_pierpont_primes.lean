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
# Pierpont primes

A Pierpont prime is a prime of the form $2^a 3^b + 1$, where $a$ and $b$ are
nonnegative integers. Marc Gleason conjectured that there are infinitely many.

*References:*
- [Wikipedia, Pierpont prime](https://en.wikipedia.org/wiki/Pierpont_prime)
- [OEIS A005109](https://oeis.org/A005109)
-/

namespace PierpontPrime

/-- A Pierpont prime is a prime of the form $2^a3^b + 1$. -/
def IsPierpontPrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ a b : ℕ, p = 2 ^ a * 3 ^ b + 1

/-- There are infinitely many Pierpont primes. -/
theorem infinitely_many_pierpont_primes :
    Set.Infinite {p : ℕ | IsPierpontPrime p} := by
  sorry

end PierpontPrime

theorem PierpontPrime.infinitely_many_pierpont_primes.disproof : ¬ (type_of% @PierpontPrime.infinitely_many_pierpont_primes) := sorry
