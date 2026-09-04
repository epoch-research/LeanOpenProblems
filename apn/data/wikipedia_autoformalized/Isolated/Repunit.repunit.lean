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
theorem repunit :
    ∀ b : ℤ, ¬IsPerfectPower b → (∀ k : ℤ, b ≠ -4 * k ^ 4) →
      {n : ℕ | Prime (generalizedRepunit b n)}.Infinite := by
  sorry

end Repunit

theorem Repunit.repunit.disproof : ¬ (type_of% @Repunit.repunit) := sorry
