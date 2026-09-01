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
# Prime gaps

Differences between consecutive primes: $a(n) = p_{n+1} - p_n$.

*References:*
- [A001223](https://oeis.org/A001223)
-/

namespace OeisA1223

/-- Prime gaps: differences between consecutive primes. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1)

/-- Helper definition for extracting a finite subsequence (pattern) as a list. -/
noncomputable def gapSubsequence (startIndex length : ℕ) : List ℕ :=
  (List.range length).map (fun i => a (startIndex + i))

/--
Any subsequence a(n .. n+m) with n > 2 (as to exclude the
untypical primes 2 and 3) should occur infinitely many times at other starting points k.
-/
theorem conjecture (n m : ℕ) (hn : n ≥ 3) :
    Set.Infinite {k : ℕ | gapSubsequence k (m + 1) = gapSubsequence n (m + 1)} := by
  sorry

end OeisA1223

theorem OeisA1223.conjecture.disproof : ¬ (type_of% @OeisA1223.conjecture) := sorry
