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

open Nat

/-!
# Erdős Problem 1056

*Reference:* [erdosproblems.com/1056](https://www.erdosproblems.com/1056)
-/

namespace Erdos1056

/--
The proposition that the modular product of a collection of consecutive interval equals $1$ modulo $p$,
where intervals are defined by a function specifying the consecutive boundaries.
-/
def AllModProdEqualsOne (p : ℕ) {k : ℕ} (boundaries : Fin (k + 1) → ℕ) : Prop :=
  ∀ i : Fin k,
    (∏ n ∈ Finset.Ico (boundaries i.castSucc) (boundaries (i.castSucc + 1)), n) ≡ 1 [MOD p]

/--
Noll and Simmons asked, more generally, whether there are solutions to
$q_1! \equiv \dots \equiv q_k! \mod p$ for arbitrarily large $k$ (with $q_1 < \dots < q_k$).
-/
theorem erdos_1056.variants.noll_simmons :
    ∀ᶠ k in Filter.atTop,
    ∃ (p : ℕ) (_ : p.Prime) (Q : Fin k → ℕ) (_ : StrictMono Q) (_ : ∀ i, Q i < p),
    ∀ i j : Fin k, (Q i)! ≡ (Q j)! [MOD p] := by
  sorry

end Erdos1056
