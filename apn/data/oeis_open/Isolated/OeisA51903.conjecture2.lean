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
# Maximum exponent in the prime factorization of $n$

*References:*
- [A051903](https://oeis.org/A051903)-/

namespace OeisA51903

/-- Maximum exponent in the prime factorization of $n$. -/
def a (n : ℕ) : ℕ :=
  (n.primeFactorsList.map (n.primeFactorsList.count ·)).foldr max 0

/--
Are there odd numbers $n$ such that $a(n) > 1$ and $n \equiv a(n) \pmod{\lambda(n)}$?
(Equivalently, odd numbers $n$ such that $a(n) > 1$ and $b^n \equiv b^{a(n)} \pmod n$ for all $b$.)
- Thomas Ordowski, Dec 02 2019
-/
theorem conjecture2 :
    ∃ n : ℕ, Odd n ∧ 1 < a n ∧ ∀ b : ℕ, b ^ n ≡ b ^ (a n) [MOD n] := by
  sorry

end OeisA51903

theorem OeisA51903.conjecture2.disproof : ¬ (type_of% @OeisA51903.conjecture2) := sorry
