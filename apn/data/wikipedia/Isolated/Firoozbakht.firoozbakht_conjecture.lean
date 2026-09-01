/-
Copyright 2025 The Formal Conjectures Authors.

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
# Firoozbakht's conjecture

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Firoozbakht%27s_conjecture)
- [primepuzzles](https://www.primepuzzles.net/conjectures/conj_030.htm)
-/

open Real

namespace Firoozbakht

/--
The sequence of $\sqrt[n]{p_n}$ where $p_n$ is the n:th prime number.
-/
noncomputable def firoozbakhtSeq (n : ℕ) : ℝ :=
  (n.nth Prime)^(1/(n + 1) : ℝ)

/--
**Firoozbakht's conjecture**
The inequality $\sqrt[n+1]{p_{n+1}} < \sqrt[n]{p_n}$ holds for all prime numbers $p_n$.
-/
theorem firoozbakht_conjecture (n : ℕ) :
    firoozbakhtSeq (n+1) < firoozbakhtSeq n := by
  sorry

end Firoozbakht

theorem Firoozbakht.firoozbakht_conjecture.disproof : ¬ (type_of% @Firoozbakht.firoozbakht_conjecture) := sorry
