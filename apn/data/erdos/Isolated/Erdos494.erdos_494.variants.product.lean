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
# Erdős Problem 494

*References:*
  - [erdosproblems.com/494](https://www.erdosproblems.com/494)
  - [SeSt58] Selfridge, J. L. and Straus, E., On the determination of numbers by their sums
      of a fixed order. Pacific Journal of Math. (1958), 847-856.
  - [Er61] Erdős, Paul, Some unsolved problems. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
      221-254.
  - [GFS62] Gordon, B. and Fraenkel, A. S. and Straus, E. G., On the determination of sets
      by the sets of sums of a certain order. Pacific J. Math. (1962), 187--196.
-/

open Filter

namespace Erdos494

/--
For a finite set $A \subset \mathbb{C}$ and $k \ge 1$, define $A_k$ as the multiset consisting of
all sums of $k$ distinct elements of $A$.
-/
noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def Erdos494Unique (k : ℕ) (card : ℕ) :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card → sumMultiset A k = sumMultiset B k → A = B

/--
A version in [Er61] by Erdős is product instead of sum, which is false.
Counterexample (by Steinerberger): consider $k = 3$ and let
$A = \{1, \zeta_6, \zeta_6^2, \zeta_6^4\}$ and $B = \{1, \zeta_6^2, \zeta_6^3, \zeta_6^4\}$.
-/
noncomputable def prodMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  ((A.powersetCard k).val.map (fun s => s.prod id))

/-- A counterexample to the product version of the conjecture (by Steinerberger). -/
theorem erdos_494.variants.product :
    ∃ (A B : Finset ℂ), A.card = B.card ∧ prodMultiset A 3 = prodMultiset B 3 ∧
      A ≠ B := by
  sorry

end Erdos494
