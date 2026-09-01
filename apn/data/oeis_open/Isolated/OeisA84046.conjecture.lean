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
# Smallest prime $p$ such that $p + n$ is an $n$-th power

Smallest prime $p$ such that $p + n$ is an $n$-th power, or $0$ if no such number exists.
That is, the smallest prime of the form $k^n - n$.

*References:*
- [A084046](https://oeis.org/A084046)-/

namespace OeisA84046

/-- Smallest prime $p$ such that $p + n$ is an $n$-th power, or $0$ if no such prime exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ ∃ k : ℕ, k ^ n = p + n}

/--
Conjecture: if a(k) = 0 then k is an even square.-/
theorem conjecture (k : ℕ) (h : a k = 0) : ∃ m : ℕ, k = (2 * m) ^ 2 := by
  sorry

end OeisA84046

theorem OeisA84046.conjecture.disproof : ¬ (type_of% @OeisA84046.conjecture) := sorry
