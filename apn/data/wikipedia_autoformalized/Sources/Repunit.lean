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
# Repunit primes to a general base

For an integer base $b$ with $|b| \ge 2$ and $n \ge 1$, the base-$b$ repunit is
$$R_n^{(b)} = 1 + b + b^2 + \cdots + b^{n-1} = \frac{b^n - 1}{b - 1},$$
the number written with $n$ digits $1$ in base $b$. The base $b$ may be negative, in which case
$R_n^{(b)}$ is negative for even $n$, so a repunit prime to base $b$ is a repunit that is prime
up to sign. The base-$2$ repunit primes are the Mersenne primes.

Two families of bases carry no hope of infinitely many repunit primes. If $b = m^k$ is a perfect
power (with $m, k$ integers and $k > 1$), then at most one base-$b$ repunit is prime. If
$b = -4k^4$, then the repunits have an aurifeuillean factorisation. The conjecture is that these
are the only obstructions.

*References:*
* [Wikipedia: Repunit](https://en.wikipedia.org/wiki/repunit)
* [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
-/

namespace Repunit

/-- The base-`b` repunit with `n` digits,
$R_n^{(b)} = \sum_{i < n} b^i = \frac{b^n - 1}{b - 1}$, for an integer base `b`. -/
def generalizedRepunit (b : ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, b ^ i

/-- An integer `b` is a perfect power if `b = m ^ k` for some integer `m` and some integer
`k > 1`, following the definition in the Wikipedia article. In particular `0`, `1` and `-1` are
perfect powers, as is `-8 = (-2) ^ 3`, whereas `-4` and `-16` are not. -/
def IsPerfectPower (b : ℤ) : Prop :=
  ∃ m : ℤ, ∃ k : ℕ, 1 < k ∧ m ^ k = b

/--
For any given integer $b$ which is not a perfect power and not of the form $-4k^4$ for an
integer $k$, are there infinitely many repunit primes to base $b$?

Here a repunit prime to base $b$ is a repunit $R_n^{(b)} = \frac{b^n - 1}{b - 1}$ with $n \ge 1$
that is prime, where for negative $b$ primality is taken up to sign (`Prime` in $\mathbb{Z}$).
Infinitely many repunit primes means infinitely many $n$ with $R_n^{(b)}$ prime; since
$|R_n^{(b)}|$ is eventually strictly increasing in $n$, this is the same as infinitely many
distinct primes. The degenerate bases $b = 0, \pm 1$, for which repunits are not defined, are
perfect powers and so are excluded by the hypotheses.
-/
@[category research open, AMS 11]
theorem repunit :
    answer(sorry) ↔ ∀ b : ℤ, ¬IsPerfectPower b → (∀ k : ℤ, b ≠ -4 * k ^ 4) →
      {n : ℕ | Prime (generalizedRepunit b n)}.Infinite := by
  sorry

/-- The decimal repunit with three digits is $111$. -/
@[category test, AMS 11]
theorem generalizedRepunit_ten_three : generalizedRepunit 10 3 = 111 := by
  decide

/-- The two-digit repunit in base `b` is `b + 1`. -/
@[category test, AMS 11]
theorem generalizedRepunit_two (b : ℤ) : generalizedRepunit b 2 = b + 1 := by
  simp [generalizedRepunit, Finset.sum_range_succ, add_comm]

/-- The repunit with no digits is $0$, so `n = 0` never contributes a repunit prime. -/
@[category test, AMS 11]
theorem generalizedRepunit_zero (b : ℤ) : generalizedRepunit b 0 = 0 := by
  simp [generalizedRepunit]

/-- Base-$2$ repunits are the Mersenne numbers: $R_5^{(2)} = 31$ is a Mersenne prime. -/
@[category test, AMS 11]
theorem prime_generalizedRepunit_two_five : Prime (generalizedRepunit 2 5) := by
  rw [Int.prime_iff_natAbs_prime]
  decide

/-- The base-$(-3)$ repunit $R_2^{(-3)} = -2$ is negative but prime up to sign. -/
@[category test, AMS 11]
theorem prime_generalizedRepunit_neg_three_two : Prime (generalizedRepunit (-3) 2) := by
  rw [Int.prime_iff_natAbs_prime]
  decide

/-- The degenerate bases `0`, `1` and `-1` are perfect powers, so they are excluded from the
conjecture. -/
@[category test, AMS 11]
theorem isPerfectPower_degenerate :
    IsPerfectPower 0 ∧ IsPerfectPower 1 ∧ IsPerfectPower (-1) :=
  ⟨⟨0, 2, by norm_num⟩, ⟨1, 2, by norm_num⟩, ⟨-1, 3, by norm_num⟩⟩

/-- Negative bases can be perfect powers: `-8 = (-2) ^ 3`. -/
@[category test, AMS 11]
theorem isPerfectPower_neg_eight : IsPerfectPower (-8) :=
  ⟨-2, 3, by norm_num⟩

/-- The base `2` satisfies both hypotheses of the conjecture, so they are not vacuous. -/
@[category test, AMS 11]
theorem two_satisfies_hypotheses : ¬IsPerfectPower 2 ∧ ∀ k : ℤ, 2 ≠ -4 * k ^ 4 := by
  refine ⟨?_, fun k h => ?_⟩
  · rintro ⟨m, k, hk, h⟩
    have h' : m.natAbs ^ k = 2 := by
      rw [← Int.natAbs_pow, h]
      rfl
    have := (Nat.prime_two.pow_eq_iff.mp h').2
    omega
  · have : 0 ≤ k ^ 4 := by positivity
    omega

end Repunit
