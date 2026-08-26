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
# Product of two consecutive primes modulo the next prime

The sequence is defined by
$$a(n) = \mathrm{prime}(n) \cdot \mathrm{prime}(n+1) \bmod \mathrm{prime}(n+2),$$
where $\mathrm{prime}(k)$ is the $k$-th prime number ($\mathrm{prime}(1)=2$).

*References:*
- [A182126](https://oeis.org/A182126)-/

namespace OeisA182126

/-- $\mathrm{prime}(k)$ is the $k$-th prime number ($\mathrm{prime}(1) = 2$). -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- $a(n) = \mathrm{prime}(n) \cdot \mathrm{prime}(n+1) \bmod \mathrm{prime}(n+2)$. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else (prime n * prime (n + 1)) % prime (n + 2)

/-- Count of occurrences of value $v$ among $a(1), \dots, a(x)$. -/
noncomputable def countA (x v : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => 1 ≤ n ∧ a n = v).card

/-- $v_0$ is a most frequent value among $a(1), \dots, a(x)$. -/
def IsMostFrequent (x v₀ : ℕ) : Prop :=
  ∀ v : ℕ, countA x v ≤ countA x v₀

/--
Let $b = \mathrm{prime}(n+2) - \mathrm{prime}(n)$ and $c = \mathrm{prime}(n+2) - \mathrm{prime}(n+1)$.
Conjecture: for $n > 61$, $a(n) = b \cdot c$.
- _Charles R Greathouse IV_, May 11 2012
-/
theorem conjecture2 (n : ℕ) (hn : 61 < n) :
    let b := prime (n + 2) - prime n
    let c := prime (n + 2) - prime (n + 1)
    a n = b * c := by
  sorry

end OeisA182126
