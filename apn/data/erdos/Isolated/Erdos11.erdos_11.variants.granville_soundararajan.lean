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
# Erdős Problem 11

*Reference:* [erdosproblems.com/11](https://www.erdosproblems.com/11)
-/

namespace Erdos11

/--
Suppose that every odd $n$ is the sum of a squarefree number and a power of 2. Then the set of primes
$p$ such that $2 ^ p ≡ 2 \mod p ^ 2$ is infinite. This is Theorem 1 in [GrSo98].
[GrSo98] Granville, A. and Soundararajan, K., A Binary Additive Problem of Erdős and the Order of $2$ mod $p^2$. The Ramanujan Journal (1998), 283-298.
-/
theorem erdos_11.variants.granville_soundararajan (H : type_of% erdos_11) :
    {p : ℕ | p.Prime ∧ 2 ^ p ≡ 2 [MOD p ^ 2]}.Infinite := by
  sorry

end Erdos11
