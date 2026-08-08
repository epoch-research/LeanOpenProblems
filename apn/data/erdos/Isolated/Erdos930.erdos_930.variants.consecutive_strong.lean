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
# Erdős Problem 930

*Reference:* [erdosproblems.com/930](https://www.erdosproblems.com/930)
-/

open Finset

namespace Erdos930

/--
$n$ is a perfect power if there exist natural numbers $m$ and $l$
such that $1 < l$ and $m^l = n$.
-/
def IsPower (n : ℕ) : Prop :=
  ∃ m l, 1 < l ∧ m^l = n

/--
Returns the least prime satisfying $k \le p$
-/
def nextPrime (k : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes k)

/--
Let $k$, $l$, $n$ be integers such that $k \ge 3$, $l \ge 2$ and $n + k \ge p^{(k)}$,
where $p^{(k)}$ is the least prime satisfying $p^{(k)} \ge k$.
Then there is a prime $p \ge k$ for which $l$ does not divide
the multiplicity of the prime factor $p$ in $(n + 1) \ldots (n + k)$.

Theorem 2 from [ErSe75].

[ErSe75] Erdős, P. and Selfridge, J. L., The product of consecutive integers is never a power. Illinois J. Math. (1975), 292-301.
-/
theorem erdos_930.variants.consecutive_strong :
    ∀ k l n, 3 ≤ k → 2 ≤ l → nextPrime k ≤ n + k →
      ∃ p, k ≤ p ∧ p.Prime ∧
        ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n + 1) (n + k), m) p) := by
  sorry

end Erdos930
