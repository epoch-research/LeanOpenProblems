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
# Number of prime powers strictly between $n$-th prime and $(n+1)$-th prime

The sequence $a(n)$ is the number of prime powers $k$ strictly between the $n$-th prime $p_n$
and the $(n+1)$-th prime $p_{n+1}$: $p_n < k < p_{n+1}$.

*References:*
- [A080101](https://oeis.org/A080101)-/

namespace OeisA80101

open Finset

/-- Number of prime powers strictly between the $n$-th prime and the $(n+1)$-th prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let pn := Nat.nth Nat.Prime (n - 1)
    let pn1 := Nat.nth Nat.Prime n
    ((Ioo pn pn1).filter IsPrimePow).card

/--
It is conjectured that $a(n) \le 2$ for all $n$.-/
theorem conjecture (n : ℕ) : a n ≤ 2 := by
  sorry

end OeisA80101

theorem OeisA80101.conjecture.disproof : ¬ (type_of% @OeisA80101.conjecture) := sorry
