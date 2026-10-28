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
# Emirps

An emirp is a prime whose decimal reversal is a different prime. It is unknown whether there are
infinitely many emirps.

*References:*
* [Wikipedia, Emirp](https://en.wikipedia.org/wiki/Emirp)
* [OEIS A006567](https://oeis.org/A006567)
-/

namespace Emirp

/-- Reverse the base-ten digits of a natural number. -/
def reverse10 (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- A natural number is an emirp if it and its distinct decimal reversal are both prime. -/
def IsEmirp (p : ℕ) : Prop :=
  p.Prime ∧ (reverse10 p).Prime ∧ reverse10 p ≠ p

/-- [Wikipedia's article on emirps](https://en.wikipedia.org/wiki/Emirp) states: "It is not known
whether there are infinitely many emirps." -/
theorem infinitude_question :
    {p : ℕ | IsEmirp p}.Infinite := by
  sorry

end Emirp

theorem Emirp.infinitude_question.disproof : ¬ (type_of% @Emirp.infinitude_question) := sorry
