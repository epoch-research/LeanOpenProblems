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
# Home primes (OEIS A037274)

Starting from an integer $n\geq 2$, list its prime factors in nondecreasing order with
multiplicity, concatenate their decimal representations, and repeat. The home-prime conjecture
says that this process always reaches a prime.

For example,

$$25 \longmapsto 55 \longmapsto 511 \longmapsto 773.$$

*References:*
* [OEIS A037274](https://oeis.org/A037274)
* M. Herman and J. Schiffman, *Investigating home primes and their families*,
  Mathematics Teacher 107 (2014), 606–614
-/

namespace OeisA37274

/-- The number of decimal digits of a natural number, counting zero as one digit. -/
def decimalDigitCount (n : ℕ) : ℕ :=
  if n = 0 then 1 else (Nat.digits 10 n).length

/-- Append the decimal digits of `b` to those of `a`. -/
def decimalAppend (a b : ℕ) : ℕ :=
  a * 10 ^ decimalDigitCount b + b

/-- Concatenate the prime factors of `n` in nondecreasing order, retaining multiplicity. -/
def primeFactorSplice (n : ℕ) : ℕ :=
  n.primeFactorsList.foldl decimalAppend 0

/-- A starting value reaches a prime after finitely many prime-factor splicing steps. -/
def ReachesPrime (n : ℕ) : Prop :=
  ∃ k : ℕ, ((primeFactorSplice^[k]) n).Prime

/-- Every integer at least two reaches a home prime. -/
theorem home_prime_conjecture : ∀ n : ℕ, 2 ≤ n → ReachesPrime n := by
  sorry

end OeisA37274
