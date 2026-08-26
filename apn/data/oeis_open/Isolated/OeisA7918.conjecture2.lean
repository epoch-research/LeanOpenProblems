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
# Least prime $\ge n$

Least prime $\ge n$ (version 1 of the "next prime" function).

*References:*
- [A007918](https://oeis.org/A007918)
-/

namespace OeisA7918

/-- Least prime $\ge n$ (version 1 of the "next prime" function). -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { p : ℕ | p.Prime ∧ n ≤ p }

/--
The initial term $p_0$ and common difference $d$ form an arithmetic progression of
length $n$ consisting entirely of prime numbers with $d > 0$.
-/
def isApOfNPrimes (n p0 d : ℕ) : Prop :=
  d > 0 ∧ ∀ k < n, (p0 + k * d).Prime

/--
If $n > 1$, then $a(n) < n^{n^{1/n}}$.
- Thomas Ordowski, Feb 23 2023
-/
theorem conjecture2 (n : ℕ) (hn : 1 < n) :
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  sorry

end OeisA7918
