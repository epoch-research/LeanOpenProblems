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
# Palindromic primes

A *palindromic prime* is a prime number whose digit string, in a given base $b \ge 2$, reads the
same forwards and backwards. The first few decimal palindromic primes are
$2, 3, 5, 7, 11, 101, 131, 151, \ldots$ ([A002385](https://oeis.org/A002385)).
Banks, Hart and Sakata showed that, in every base, almost all palindromes are composite, but it is
not known whether there are infinitely many palindromic primes in any single base.

*References:*
- [Wikipedia, Palindromic prime](https://en.wikipedia.org/wiki/palindromic_prime)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Banks, Hart, Sakata, *Almost all palindromes are composite*](https://arxiv.org/abs/math/0405056)
-/

namespace PalindromicPrime

/--
Are there infinitely many palindromic primes to every base?

That is, is it true that for every base $b \ge 2$ there are infinitely many primes $p$ whose
base-$b$ digit string (without leading zeros, as given by `Nat.digits`) is a palindrome?

The restriction $b \ge 2$ excludes the degenerate "bases" $0$ and $1$, for which `Nat.digits`
does not give a positional numeral system.
-/
@[category research open, AMS 11]
theorem palindromic_prime :
    answer(sorry) ↔
      ∀ b ≥ 2, {p : ℕ | p.Prime ∧ (Nat.digits b p).Palindrome}.Infinite := by
  sorry

/-- Sanity check: $131$ is a decimal palindromic prime. -/
@[category test, AMS 11]
theorem palindromic_prime_131 : 131 ∈ {p : ℕ | p.Prime ∧ (Nat.digits 10 p).Palindrome} := by
  refine ⟨by norm_num, ?_⟩
  rw [List.Palindrome.iff_reverse_eq]
  norm_num

/-- Sanity check: $13$ is prime but is not a decimal palindrome. -/
@[category test, AMS 11]
theorem not_palindromic_prime_13 : 13 ∉ {p : ℕ | p.Prime ∧ (Nat.digits 10 p).Palindrome} := by
  simp only [Set.mem_setOf_eq, not_and, List.Palindrome.iff_reverse_eq]
  intro _
  norm_num

/-- Sanity check: $7 = 111_2$ is a binary palindromic prime (a Mersenne prime). -/
@[category test, AMS 11]
theorem palindromic_prime_binary_7 : 7 ∈ {p : ℕ | p.Prime ∧ (Nat.digits 2 p).Palindrome} := by
  refine ⟨by norm_num, ?_⟩
  rw [List.Palindrome.iff_reverse_eq]
  norm_num

end PalindromicPrime
