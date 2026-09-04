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
# Waring's problem

For a positive integer $k$, let $g(k)$ be the least $s$ such that every positive integer is a sum
of at most $s$ $k$-th powers of positive integers, and let $G(k)$ be the least $s$ such that
every sufficiently large positive integer is a sum of at most $s$ $k$-th powers of positive
integers. The Hilbert–Waring theorem states that $g(k)$ (hence $G(k)$) is finite for every $k$.
The open problem is to determine the values of $g(k)$ and $G(k)$.

*References:*
- [Wikipedia: Waring's problem](https://en.wikipedia.org/wiki/Waring%27s_problem)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [OEIS A002804](https://oeis.org/A002804)
-/

namespace WaringsProblem

open Set

/-- The set of $k$-th powers of natural numbers. It contains $0 = 0^k$ for $k \ge 1$, so a sum
of exactly $s$ elements of `kthPowers k` is the same as a sum of at most $s$ $k$-th powers of
positive integers. -/
def kthPowers (k : ℕ) : Set ℕ := range fun n : ℕ => n ^ k

/-- The Waring number $g(k)$: the least $s$ such that every natural number is a sum of exactly
$s$ elements of `kthPowers k`, i.e. a sum of at most $s$ $k$-th powers of positive integers.
For $k \ge 1$ the Hilbert–Waring theorem shows that such an $s$ exists. -/
noncomputable def g (k : ℕ) : ℕ := sInf {s | (kthPowers k).IsAddBasisOfOrder s}

/-- The number $G(k)$: the least $s$ such that every sufficiently large natural number is a sum
of exactly $s$ elements of `kthPowers k`, i.e. a sum of at most $s$ $k$-th powers of positive
integers. Note that in `ℕ` the `cofinite` filter used by `Set.IsAsymptoticAddBasisOfOrder`
coincides with `Filter.atTop`. -/
noncomputable def G (k : ℕ) : ℕ := sInf {s | (kthPowers k).IsAsymptoticAddBasisOfOrder s}

/-- Write $3^k = 2^k q + r$ with $0 \le r < 2^k$, i.e. $q = \lfloor (3/2)^k \rfloor$ and
$r = 2^k \{(3/2)^k\}$. The Dickson–Pillai–Rubugunday–Niven formula gives
$g(k) = 2^k + q - 2$ whenever $q + r \le 2^k$, and a different value otherwise. No $k$ with
$q + r > 2^k$ is known, Mahler proved there are only finitely many such $k$, and Kubina and
Wunderlich showed any such $k$ satisfies $k > 471\,600\,000$. It is conjectured that there are
no such $k$: for every positive integer $k$, $q + r \le 2^k$.
Here `3 ^ k / 2 ^ k` and `3 ^ k % 2 ^ k` are the quotient $q$ and the remainder $r$. -/
theorem warings_problem.variants.no_exceptional_k (k : ℕ) (hk : 0 < k) :
    3 ^ k / 2 ^ k + 3 ^ k % 2 ^ k ≤ 2 ^ k := by
  sorry

end WaringsProblem

theorem WaringsProblem.warings_problem.variants.no_exceptional_k.disproof : ¬ (type_of% @WaringsProblem.warings_problem.variants.no_exceptional_k) := sorry
