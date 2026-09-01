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
# Product of composite numbers in triangular intervals

Product of all composite numbers between $n(n-1)/2+1$ and $n(n+1)/2$ (including boundaries),
where $n(n-1)/2 = \binom{n}{2}$ and $n(n+1)/2 = \binom{n+1}{2}$.

*References:*
- [A093456](https://oeis.org/A093456)-/

namespace OeisA93456

/-- Product of all composite numbers in the interval $[\binom{n}{2} + 1, \binom{n+1}{2}]$. -/
def a (n : ℕ) : ℕ :=
  let L := n.choose 2 + 1
  let R := (n + 1).choose 2
  ((Finset.Icc L R).filter fun k => 1 < k ∧ ¬ k.Prime).prod id

/--
Conjecture: There are finitely many numbers such that $a(n)$ is not $\equiv 0 \pmod{a(n-1)}$.
(Also mentioned in A093455.)-/
theorem conjecture :
    Set.Finite {n : ℕ | 1 < n ∧ ¬ (a (n - 1) ∣ a n)} := by
  sorry

end OeisA93456

theorem OeisA93456.conjecture.disproof : ¬ (type_of% @OeisA93456.conjecture) := sorry
