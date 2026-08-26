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
# Collatz step differences

Differences in adjacent elements of the sequence quantifying the steps needed for $n$ to
converge to 1 in the Collatz Conjecture.
$$a(n) = \mathrm{A006577}(n+1) - \mathrm{A006577}(n)$$
for $n > 0$.

*References:*
- [A153330](https://oeis.org/A153330)-/

namespace OeisA153330

/-- Single step of the Collatz mapping. -/
def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

open Classical in
/-- Number of iterations required to turn $n$ into 1 in the Collatz process,
or `none` if $n$ does not terminate. -/
noncomputable def collatzSteps (n : ℕ) : Option ℕ :=
  if n = 0 then none
  else if ∃ k : ℕ, (collatzStep^[k]) n = 1 then
    some (sInf {k : ℕ | (collatzStep^[k]) n = 1})
  else
    none

open Classical in
/-- The sequence $a(n) = \mathrm{A006577}(n+1) - \mathrm{A006577}(n)$ for $n > 0$,
or `none` if either $n$ or $n+1$ does not terminate. -/
noncomputable def a (n : ℕ) : Option ℤ :=
  if n = 0 then none
  else
    match collatzSteps (n + 1), collatzSteps n with
    | some s2, some s1 => some (s2 - s1)
    | _, _ => none

/-- The set of positive indices $n$ for which $a(n) = v$. -/
def indices (v : ℤ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ a n = some v}

/--
Conjecture 3 (Ya-Ping Lu, 2024):
Except 1, 3 and 6, the absolute value of all terms can be written as $5x + 8y$ for $x, y \in \mathbb{N}$.
(Note: in the OEIS comment, "x and y are integers" means $x$ and $y$ have the same sign,
i.e., $|v| = 5x + 8y$ with $x, y \ge 0$, since every integer is a $\mathbb{Z}$-linear combination of 5 and 8).
-/
theorem conjecture3 (n : ℕ) (v : ℤ) (hn : 0 < n) (ha : a n = some v)
    (hv : v ≠ 1 ∧ v ≠ 3 ∧ v ≠ 6) :
    ∃ x y : ℕ, v.natAbs = 5 * x + 8 * y := by
  sorry

end OeisA153330
