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
# Erdős Problem 939

*Reference:* [erdosproblems.com/939](https://www.erdosproblems.com/939)
-/
open Nat

namespace Erdos939

/--
A set `S` belongs to `Erdos939Sums r` if it meets the following criteria:
- The size of the set is `$|S| = r - 2$`.
- The elements of the set are coprime (their greatest common divisor is 1).
- Every element in `S` is an `$r$-powerful` number.
- The sum of the elements in `S`, i.e., `$\sum_{s \in S} s$`, is also an `$r$-powerful` number.
-/
def Erdos939Sums (r : ℕ) :=
    {S : Finset ℕ | S.card = r - 2 ∧ S.Coprime ∧ r.Full (∑ s ∈ S, s) ∧ ∀ s ∈ S, r.Full s}

/-- Cambie has also found solutions when $r=7$. -/
theorem erdos_939.variants.seven : (Erdos939Sums 7).Nonempty := by
  sorry

end Erdos939
