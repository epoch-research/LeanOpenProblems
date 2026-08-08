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
import FormalConjectures.Wikipedia.Schinzel

/-!
# Erdős Problem 252

*References:*
 - [erdosproblems.com/252](https://www.erdosproblems.com/252)
 - [ErSt71] Erdös, P., and E. G. Straus. "Some number theoretic results." Pacific J. Math 36 (1971):
    635-646.
 - [ErSt74] Erdős, Paul, and Ernst Straus. "On the irrationality of certain series." Pacific journal
    of mathematics 55.1 (1974): 85-92.
 - [ErKa54] P. Erdős, M. Kac, Amer. Math. Monthly 61 (1954), Problem 4518.
 - [ScPu06] Schlage-Puchta, J. C., The irrationality of a number theoretical series. Ramanujan J.
    (2006), 455-460.
 - [FLC07] Friedlander, J. B. and Luca, F. and Stoiciu, M., On the irrationality of a divisor
    function series. Integers (2007).
 - [Pr22] Pratt, K., The irrationality of a divisor function series of Erdős and Kac.
    arXiv:2209.11124 (2022).
-/

open scoped Nat ArithmeticFunction.sigma

namespace Erdos252

/-- The series `∑ σ k n / n!`. -/
noncomputable def erdos_252_sum (k : ℕ) : ℝ := ∑' n, σ k n / (n ! : ℝ)

/-- If Schinzel's conjecture is true, then `∑ σ k n / n!` is irrational for all `k`. This is proved
in [ScPu06]. -/
theorem erdos_252.variants.schinzel (hs : ∀ (fs : Finset (Polynomial ℤ)),
    (∀ f ∈ fs, BunyakovskyCondition f) → SchinzelCondition fs →
    Infinite ↑{n | ∀ f ∈ fs, Prime (Polynomial.eval (↑n) f).natAbs}) :
    ∀ k, Irrational (erdos_252_sum k) := by
  sorry

end Erdos252
