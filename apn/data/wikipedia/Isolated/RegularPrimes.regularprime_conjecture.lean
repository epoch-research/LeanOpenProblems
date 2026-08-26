/-
Copyright 2025 The Formal Conjectures Authors.

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
# Infinite Regular Primes

We define the notion of regular primes, which are prime numbers that are coprime with the
cardinality of the class group of the `p`-th cyclotomic field. We also state that there are
infinitely many regular primes.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Regular_prime)
-/

open scoped NumberField

variable (p : ℕ)

namespace RegularPrimes

/-- A natural prime number `p` is regular if `p` is coprime with the order of the class group
of the `p`-th cyclotomic field. -/
noncomputable def IsRegularPrime [Fact p.Prime] : Prop :=
  p.Coprime <| Fintype.card <| ClassGroup (𝓞 <| CyclotomicField p ℚ)

/-- The set of regular primes. -/
def regularPrimes : Set ℕ := { p | ∃ (hp : Nat.Prime p), @IsRegularPrime p ⟨hp⟩ }

/-- The set of irregular primes. -/
def irregularPrimes : Set ℕ := { p | ∃ (hp : Nat.Prime p), ¬ @IsRegularPrime p ⟨hp⟩ }

/-- Conjecture: The set of regular primes is infinite. -/
def RegularPrimeConjecture : Prop :=
  regularPrimes.Infinite

/-- Conjecture: The set of regular primes is infinite. -/
theorem regularprime_conjecture : RegularPrimeConjecture := by
  sorry

end RegularPrimes
