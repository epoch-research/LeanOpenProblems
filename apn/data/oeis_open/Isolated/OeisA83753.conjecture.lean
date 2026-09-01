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
# Smallest palindrome with exactly $n$ divisors

The sequence $a(n)$ is the smallest palindromic number with exactly $n$ divisors, or $0$
if no such number exists.

*References:*
- [A083753](https://oeis.org/A083753)-/

namespace OeisA83753

/-- A natural number $m$ is a decimal palindrome if its base-$10$ digits read the same
forwards and backwards. -/
def IsDecimalPalindrome (m : ℕ) : Prop :=
  Nat.digits 10 m = (Nat.digits 10 m).reverse

instance (m : ℕ) : Decidable (IsDecimalPalindrome m) :=
  inferInstanceAs (Decidable (Nat.digits 10 m = (Nat.digits 10 m).reverse))

open Classical in
/-- Smallest positive palindrome with exactly $n$ divisors, or $0$ if no such number exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ m, 0 < m ∧ IsDecimalPalindrome m ∧ (Nat.divisors m).card = n then
    Nat.find h
  else
    0

/--
There are no palindromic numbers greater than 1 which are the fifth or higher power of a natural
number.-/
theorem conjecture (m k : ℕ) (hm : 1 < m) (hpal : IsDecimalPalindrome m) (hk : 5 ≤ k) :
    ¬ ∃ x : ℕ, m = x ^ k := by
  sorry

end OeisA83753

theorem OeisA83753.conjecture.disproof : ¬ (type_of% @OeisA83753.conjecture) := sorry
