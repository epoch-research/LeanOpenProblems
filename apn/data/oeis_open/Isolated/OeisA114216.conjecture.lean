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
# Largest odd divisor of $a(n-1) + \textrm{prime}(n)$

$a(0)=0$; thereafter $a(n)$ = largest odd divisor of $a(n-1) + \textrm{prime}(n)$.

*References:*
- [A114216](https://oeis.org/A114216)
-/

namespace OeisA114216

/--
The primary defining sequence `a`.
$a(n)$ is the largest odd divisor of $a(n-1) + \textrm{prime}(n)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n' + 1 =>
    let pN : ℕ := Nat.nth Nat.Prime n'
    let prevA : ℕ := a n'
    let sumVal : ℕ := prevA + pN
    let nu2 : ℕ := padicValNat 2 sumVal
    sumVal / (2 ^ nu2)

/--
Is $a(33900)$ the last term equal to $1$?
-/
theorem conjecture :
  ∀ n > 33900, a n ≠ 1 := by
  sorry

end OeisA114216

theorem OeisA114216.conjecture.disproof : ¬ (type_of% @OeisA114216.conjecture) := sorry
