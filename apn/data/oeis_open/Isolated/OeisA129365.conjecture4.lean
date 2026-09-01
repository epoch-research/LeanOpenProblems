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
# Ratio of product of GCDs to product of factorials of floor divisions

$$a(n) = \frac{\prod_{j=1}^n \prod_{k=1}^n \gcd(j,k)}{\prod_{k=1}^n (\lfloor n/k \rfloor!)^k}$$

*References:*
- [A129365](https://oeis.org/A129365)
-/

namespace OeisA129365

/-- $a(n) = \frac{\prod_{j=1}^n \prod_{k=1}^n \gcd(j,k)}{\prod_{k=1}^n (\lfloor n/k \rfloor!)^k}$. -/
def a (n : ℕ) : ℚ :=
  let num : ℚ := (Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k
  let den : ℚ := (Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k
  num / den

/-- Sequence A004125: sum of remainders $n \bmod k$ for $1 \le k \le n$. -/
def b (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, (n % k)

/--
Conjecture (4): Let $b(n) = \mathrm{A004125}(n) = \sum_{k=1}^n (n \bmod k)$. Then
$\mathrm{ord}_p(a(np)) = \sum_{i \ge 0} b(\lfloor n/p^i \rfloor)$.
-/
theorem conjecture4 (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ) := by
  sorry

end OeisA129365

theorem OeisA129365.conjecture4.disproof : ¬ (type_of% @OeisA129365.conjecture4) := sorry
