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
Conjecture 2: 1, 6 and 16 appear only once and 3 appears twice in the sequence,
i.e., $a(1) = 1$, $a(2) = 6$, $a(4) = a(5) = 3$, and $a(8) = 16$.
- _Ya-Ping Lu_, May 04 2024
-/
theorem conjecture2 :
    indices 1 = {1} ∧
    indices 6 = {2} ∧
    indices 16 = {8} ∧
    indices 3 = {4, 5} := by
  sorry

end OeisA153330

theorem OeisA153330.conjecture2.disproof : ¬ (type_of% @OeisA153330.conjecture2) := sorry
