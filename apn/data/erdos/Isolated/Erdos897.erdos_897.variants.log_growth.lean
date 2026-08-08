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
# Erdős Problem 897

*References:*
- [erdosproblems.com/897](https://www.erdosproblems.com/897)
- [Ar25] Archivara Math Research Agent, [An Additive Counterexample: Erdős Problem 897](https://archivara.org/paper/df04f023-6ef0-4c52-bd12-18cdaa8f0741) (2025)
- [ArWu25] Aristotle, operated mostly by L. Wu, [Lean formalisation of Erdős problem 897](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos897.lean) (2025)
- [Wi70] E. Wirsing, A characterization of $\log n$ as an additive arithmetic function.
  Symposia Math. (1970), 45-57.
- [Wi81] E. Wirsing, Additive and completely additive functions with restricted growth.
  Recent progress in analytic number theory, Vol. 2 (Durham, 1979), 231--280 (1981).
-/
-- TODO(lezeau): add `ArithmeticFunction.IsAdditive` to `ForMathlib`

namespace Erdos897

/--
Wirsing [Wi70] proved that if $|f(n+1)−f(n)| ≤ C$ then $f(n) = c \log n + O(1)$ for some constant
$c$.
-/
theorem erdos_897.variants.log_growth
    (f : ℕ → ℝ)
    (hf : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b)
    (C : ℝ) (hf' : ∀ n, |f (n+1) - f n| ≤ C) :
    ∃ c, ∃ (O : ℕ → ℝ), O =O[Filter.atTop] (1 : ℕ → ℝ) ∧
      ∀ n, f n ≤ c*Real.log n + O n := by
  sorry

end Erdos897
