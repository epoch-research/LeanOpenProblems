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
# Rudin's conjecture on squares in arithmetic progressions

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Rudin%27s_conjecture)
- [Ru60] Rudin, W., *Trigonometric series with gaps*, J. Math. Mech. 9 (1960), 203–227.
- González-Jiménez, E. and Xarles, X., *On a conjecture of Rudin on squares in arithmetic
  progressions*, LMS J. Comput. Math. 17 (2014), 58–76.
-/

open Filter Asymptotics Real

namespace RudinsConjecture

/-- $Q(N; q, a)$ is the number of perfect squares among the first $N$ terms of the arithmetic
progression $\{q n + a : 0 \le n < N\}$. -/
noncomputable abbrev Q (N q a : ℕ) : ℕ := {n : ℕ | n < N ∧ IsSquare (q * n + a)}.ncard

/-- A pair $(q, a)$ describes a *non-trivial* arithmetic progression if $q, a \ge 1$,
$\gcd(q, a) = 1$, and $(q, a) \neq (1, 1)$. -/
def IsNontrivial (q a : ℕ) : Prop :=
  1 ≤ q ∧ 1 ≤ a ∧ Nat.Coprime q a ∧ (q, a) ≠ (1, 1)

/-- $Q(N) = \max Q(N; q, a)$, the largest number of perfect squares occurring among the first
$N$ terms of any non-trivial arithmetic progression. The supremum is over a set of naturals that
is bounded above by $N$ (each progression has only $N$ terms), so it is attained. -/
noncomputable def Qmax (N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ q a : ℕ, IsNontrivial q a ∧ Q N q a = m}

/--
A stronger form of Rudin's conjecture: for every $N \ge 6$, the arithmetic progression
$24 n + 1$ attains the maximum $Q(N)$.
-/
theorem rudins_conjecture_strong (N : ℕ) (hN : 6 ≤ N) : Q N 24 1 = Qmax N := by
  sorry

end RudinsConjecture
