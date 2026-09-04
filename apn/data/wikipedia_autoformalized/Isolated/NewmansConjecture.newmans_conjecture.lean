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
# Newman's conjecture

Newman's conjecture states that the partition function $p(n)$ satisfies any arbitrary
congruence infinitely often: for all integers $m$ and $r$ with $0 \le r \le m - 1$,
there are infinitely many non-negative integers $n$ with $p(n) \equiv r \pmod m$.

*References:*
- [Wikipedia, *Newman's conjecture*](https://en.wikipedia.org/wiki/Newman%27s_conjecture)
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [M. Newman, *Periodicity Modulo m and Divisibility Properties of the Partition Function*,
  Trans. Amer. Math. Soc. 97 (1960)](https://doi.org/10.2307/1993300)
-/

namespace NewmansConjecture

/--
**Newman's conjecture.** The partition function satisfies any arbitrary congruence
infinitely often: for all integers $m$ and $r$ with $0 \le r \le m - 1$, the congruence
$p(n) \equiv r \pmod m$ holds for infinitely many non-negative integers $n$.

Here $p(n)$ is the partition function, the number of partitions of $n$ (with $p(0) = 1$),
formalised as `Fintype.card (Nat.Partition n)`. The hypothesis `r < m` is the source's
condition $0 \le r \le m - 1$ on natural numbers; it forces the modulus $m$ to be positive.
-/
theorem newmans_conjecture (m r : ℕ) (hr : r < m) :
    Set.Infinite {n : ℕ | Fintype.card (Nat.Partition n) ≡ r [MOD m]} := by
  sorry

end NewmansConjecture

theorem NewmansConjecture.newmans_conjecture.disproof : ¬ (type_of% @NewmansConjecture.newmans_conjecture) := sorry
