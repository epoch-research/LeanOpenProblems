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
# Wolstenholme Prime

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Wolstenholme_prime)
-/

namespace WolstenholmePrime

/--
A prime $p > 7$ is called a *Wolstenholme prime* if $\binom{2p-1}{p-1} \equiv 1 (\pmod{p^4})$.
-/
def IsWolstenholmePrime (p : ℕ) : Prop :=
  p > 7 ∧ p.Prime ∧ (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 4]

/--
It is conjectured that there are infinitely many Wolstenholme primes.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Wolstenholme_prime#Expected_number_of_Wolstenholme_primes)
-/
theorem wolstenholme_prime_infinite :
    {p : ℕ | IsWolstenholmePrime p}.Infinite := by
  sorry

end WolstenholmePrime
