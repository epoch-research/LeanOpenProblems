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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1074

*Reference:* [erdosproblems.com/1074](https://www.erdosproblems.com/1074)
-/

namespace Erdos1074

open scoped Nat
open Nat

/-- The EHS numbers (after Erdős, Hardy, and Subbarao) are those $m\geq 1$ such that there
exists a prime $p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$. -/
abbrev EHSNumbers : Set ℕ := {m | 1 ≤ m ∧ ∃ p, p.Prime ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

/-- The Pillai primes are those primes $p$ such that there exists an $m \ge 1$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$-/
abbrev PillaiPrimes : Set ℕ := {p | p.Prime ∧ ∃ m ≥ 1, ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

/-- Regarding the first question, Hardy and Subbarao computed all EHS numbers up to $2^{10}$, and
write "...if this trend conditions we expect [the limit] to be around 0.5, if it exists." -/
theorem erdos_1074.variants.EHSNumbers_one_half : EHSNumbers.HasDensity (1 / 2) := by
  sorry

end Erdos1074
