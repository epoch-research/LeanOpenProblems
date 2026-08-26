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
# Barker sequences

A Barker sequence is a finite sequence of $\pm 1$ values whose nontrivial aperiodic
autocorrelations all have magnitude at most one. The Barker conjecture says that no such sequence
has length greater than $13$.

*References:*
* J. Willms, [A note on Barker sequences of even length](https://arxiv.org/abs/2104.00502)
* [Barker code](https://en.wikipedia.org/wiki/Barker_code)
* [OEIS A091704](https://oeis.org/A091704)
-/

namespace Arxiv.«2104.00502»

/-- The aperiodic autocorrelation $C_k(a)=\sum_i a_i a_{i+k}$. -/
def aperiodicAutocorrelation (a : List ℤ) (k : ℕ) : ℤ :=
  (List.zipWith (· * ·) a (a.drop k)).sum

/--
A Barker sequence has $\pm 1$ entries and nontrivial autocorrelations of magnitude at most one.
-/
def IsBarkerSequence (a : List ℤ) : Prop :=
  (∀ x ∈ a, x = 1 ∨ x = -1) ∧
    ∀ k : ℕ, 0 < k → k < a.length → |aperiodicAutocorrelation a k| ≤ 1

/-- Every Barker sequence has length at most $13$. -/
theorem barker_conjecture (a : List ℤ) (ha : IsBarkerSequence a) : a.length ≤ 13 := by
  sorry

end Arxiv.«2104.00502»
