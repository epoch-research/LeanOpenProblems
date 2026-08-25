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
# Erdős Problem 457

*Reference:* [erdosproblems.com/457](https://www.erdosproblems.com/457)
-/

namespace Erdos457

/-- Let $q(n, k)$ denote the least prime which does not divide
$\prod_{1 \le i \le k}(n + i)$. -/
noncomputable abbrev q (n : ℕ) (k : ℝ) : ℕ :=
    Nat.find (Nat.exists_prime_not_dvd (∏ i ∈ Finset.Icc 1 ⌊k⌋₊, (n + i))
      (Finset.prod_ne_zero_iff.2 fun a ha => by aesop))

/--
Taking $n$ to be the product of primes
between $\log n$ and $(2 + o(1)) \log n$ gives an example where
$$
  q(n, \log n) \ge (2 + o(1)) \log n.
$$
Can one prove that $q(n, \log n) < (1 - \epsilon) (\log n)^2$
for all large $n$ and some $\epsilon > 0$?
-/
theorem erdos_457.variants.one_sub : ∃ ε > (0 : ℝ),
    ∀ᶠ n in Filter.atTop, q n (Real.log n) < (1 - ε) * Real.log n ^ 2 := by
  sorry

end Erdos457

theorem Erdos457.erdos_457.variants.one_sub.disproof : ¬ (type_of% @Erdos457.erdos_457.variants.one_sub) := sorry
