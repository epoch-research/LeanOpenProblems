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
# Imaginary part of $\prod_{k=0}^n (1 + k \cdot i)$, $i = \sqrt{-1}$

*References:*
- [A105751](https://oeis.org/A105751)
-/

open Complex Filter Topology Nat

namespace OeisA105751

/--
The primary defining sequence `a`.
a n is the imaginary part of $\prod_{k=0}^n (1 + k \cdot i)$, where $i = \sqrt{-1}$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let productTerm (k : ℕ) : ℂ := 1 + (k : ℂ) * I
  Int.floor (((Finset.range (n + 1)).prod productTerm).im)

/--
Moll's conjecture 5.5 extends to this sequence and takes the form:
(ii) for the other primes of type $2$, the p-adic valuation
$\nu_p(a(n)) \sim n/(p - 1)$ as $n \rightarrow \infty$.

(Type 2 primes consists of primes p == 1 (mod 4))
-/
theorem conjecture.variants.moll_p_mod_4_eq_1 {p : ℕ} (hp : p.Prime) (h_mod : p % 4 = 1) :
    Tendsto (fun n ↦ ((p - 1 : ℚ) * (padicValInt p (a n) : ℚ)) / (n : ℚ)) atTop (nhds 1) := by
  sorry

end OeisA105751
