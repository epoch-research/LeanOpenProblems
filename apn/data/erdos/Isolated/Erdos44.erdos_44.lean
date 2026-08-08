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
# Erdős Problem 44: Extending Sidon Sets

*Reference:* [erdosproblems.com/44](https://www.erdosproblems.com/44)
-/

open Function Set Finset

namespace Erdos44

/--
**Erdős Problem 44:** Let N ≥ 1 and `A ⊆ {1,…,N}` be a Sidon set. Is it true that, for any ε > 0,
there exist M = M(ε) and `B ⊆ {N+1,…,M}` such that `A ∪ B ⊆ {1,…,M}` is a Sidon set
of size at least `(1−ε)M^{1/2}`?

This problem asks whether any Sidon set can be extended to achieve a density
arbitrarily close to the optimal density for Sidon sets.
-/
theorem erdos_44 : ∀ᵉ (N ≥ (1 : ℕ)) (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) →
    ∀ᵉ (ε > (0 : ℝ)), ∃ᵉ (M > N) (B ⊆ Finset.Icc (N + 1) M),
      IsSidon (A ∪ B : Set ℕ) ∧ (1 - ε) * Real.sqrt M ≤ (A ∪ B).card := by
  sorry

/-  ## Related results and examples -/

end Erdos44
