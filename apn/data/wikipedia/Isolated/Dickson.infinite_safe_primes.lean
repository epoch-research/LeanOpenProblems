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
# Dickson's conjecture

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Dickson%27s_conjecture)
- [PrimePages glossary](https://t5k.org/glossary/xpage/DicksonsConjecture.html)
- [OEIS Wiki](https://oeis.org/wiki/Dickson%27s_conjecture)
- [MathWorld](https://mathworld.wolfram.com/DicksonsConjecture.html)
- [Leonard Eugene Dickson, *History of the Theory of Numbers, Vol. I: Divisibility and Primality*](https://archive.org/details/historyoftheoryo01dickuoft)
- [Arxiv](https://arxiv.org/pdf/0906.3850)
-/
open Polynomial
namespace Dickson

/-  ## Special cases -/

/--
**The infinitude of Sophie Germain primes**
There are infinitely many primes $p$ such that $2p + 1$ is prime.
-/
theorem infinite_safe_primes :
    Infinite {p : ℕ | Prime p ∧ Prime (2 * p + 1)} := by
  sorry

/-
## Other consequences
- Landau's fourth problem (primes and perfect squares)
- Twin prime conjecture
- Artin's primitive root conjecture
- First Hardy–Littlewood conjecture

*Reference:* [Arxiv](https://arxiv.org/pdf/0906.3850)
-/

end Dickson

theorem Dickson.infinite_safe_primes.disproof : ¬ (type_of% @Dickson.infinite_safe_primes) := sorry
