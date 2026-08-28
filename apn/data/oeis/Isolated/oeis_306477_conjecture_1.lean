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

import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A306477: Number of ways to write $n$ as $\binom{w+2}{2} + \binom{x+3}{4} + \binom{y+5}{6} + \binom{z+7}{8}$
with $w,x,y,z$ nonnegative integers, where $\binom{m}{k}$ denotes the binomial coefficient $\frac{m!}{k!(m-k)!}$.
-/
def A306477 (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  R.sum (fun w =>
    R.sum (fun x =>
      R.sum (fun y =>
        R.sum (fun z =>
          if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0
        )
      )
    )
  )

/--
Conjecture: a(n) > 0 for all n > 0. In other words, any positive integer n can be written as
C(w,2) + C(x,4) + C(y,6) + C(z,8), where w,x,y,z are integers greater than one.
This is also known as "the 2-4-6-8 conjecture".
-/
theorem oeis_306477_conjecture_1 : ∀ n : ℕ, 0 < n → 0 < A306477 n := by
  sorry

theorem oeis_306477_conjecture_1.disproof : ¬ (type_of% @oeis_306477_conjecture_1) := sorry
