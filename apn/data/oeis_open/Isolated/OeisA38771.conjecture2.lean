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
# Smallest composite $c$ such that $\textrm{primorial}(n) + c$ is prime

*References:*
- [A038771](https://oeis.org/A038771)
-/

open Filter Topology Real

namespace OeisA38771

/-- $a(n)$ is the smallest composite number $c$ such that $\textrm{primorial}(n) + c$ is prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  let Qn : ℕ := ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i
  let is_composite (c : ℕ) : Prop := c > 1 ∧ ¬ c.Prime
  sInf { c : ℕ | is_composite c ∧ (Qn + c).Prime }

/--
All the terms in this sequence have exactly two prime factors.
This conjecture is true for the first 133 terms.
- [Dmitry Kamenetsky](https://oeis.org/wiki/User:Dmitry_Kamenetsky), Jan 06 2019
-/
theorem conjecture2 (n : ℕ) : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ a n = p * q := by
  sorry

end OeisA38771

theorem OeisA38771.conjecture2.disproof : ¬ (type_of% @OeisA38771.conjecture2) := sorry
