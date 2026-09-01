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
# Smallest $m > 0$ such that $n \cdot 2^m + 1$ is prime

The sequence $a(n)$ is the smallest positive integer $m$ such that $n \cdot 2^m + 1$ is prime,
or $0$ if no such $m$ exists.

*References:*
- [A078680](https://oeis.org/A078680)-/

namespace OeisA78680

open Classical in
/-- Smallest $m > 0$ such that $n \cdot 2^m + 1$ is prime, or 0 if no such $m$ exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ m, 0 < m ∧ (n * 2 ^ m + 1).Prime then
    Nat.find h
  else
    0

/--
There is a conjecture that the first zero is $n = 65536 = 2^{16}$ (which is equivalent to
the statement that $2^{2^k} + 1$ is composite for $k > 4$). - _T. D. Noe_, Feb 25 2011
-/
theorem conjecture :
    a (2 ^ 16) = 0 ∧ ∀ n : ℕ, 1 ≤ n ∧ n < 2 ^ 16 → a n ≠ 0 := by
  sorry

end OeisA78680

theorem OeisA78680.conjecture.disproof : ¬ (type_of% @OeisA78680.conjecture) := sorry
