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
# Erdős Problem 137

*References:*
- [erdosproblems.com/137](https://www.erdosproblems.com/137)
-/

namespace Erdos137

/--
Erdős [Er82c] conjectures that, if $k$ is fixed, then for all $n$ sufficiently large and all
positive integers $m$, there must be at least $k$ distinct primes $p$ such that
$p\mid m(m+1)\cdots (m+n)$ and yet $p^2$ does not divide the right hand side.

[Er82c] Erdős, Paul, "Miscellaneous problems in number theory". Congr. Numer. (1982), 25-45.,
-/
theorem erdos_137.variants.multiple_powerful_factors (k : ℕ) : ∀ᶠ n in Filter.atTop,
    ∀ (m : ℕ) (hm : 0 < m),
    letI N := ∏ x ∈ Finset.Ioc m (m + n), x
    ∃ P : Finset ℕ, P.card = k ∧ ∀ p ∈ P, p.Prime ∧
    p ∣ N ∧ ¬ p ^ 2 ∣ N := by
  sorry

end Erdos137

theorem Erdos137.erdos_137.variants.multiple_powerful_factors.disproof : ¬ (type_of% @Erdos137.erdos_137.variants.multiple_powerful_factors) := sorry
