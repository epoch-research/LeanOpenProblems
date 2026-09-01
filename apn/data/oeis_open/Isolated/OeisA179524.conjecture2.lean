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
# Central binomial sum $a(n) = \sum_{k=0}^n (-4)^k \binom{n}{k}^2 \binom{n-k}{k}^2$

The sequence is defined by
$$a(n) = \sum_{k=0}^n (-4)^k \binom{n}{k}^2 \binom{n-k}{k}^2.$$

*References:*
- [A179524](https://oeis.org/A179524)
- Z.-W. Sun, "Open Conjectures on Congruences", arXiv preprint
  [arXiv:0911.5665](https://arxiv.org/abs/0911.5665) [math.NT], 2009-2011.-/

namespace OeisA179524

/-- The sequence $a(n) = \sum_{k=0}^n (-4)^k \binom{n}{k}^2 \binom{n-k}{k}^2$. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-4 : ℤ) ^ k * (n.choose k : ℤ) ^ 2 * ((n - k).choose k : ℤ) ^ 2

/--
If $p$ is a prime with $p \equiv 3, 7 \pmod{20}$ and $2p = x^2 + 5y^2$ with $x, y$ integers,
then $\sum_{k=0}^{p-1} a(k) \equiv 2x^2 - 2p \pmod{p^2}$.
- _Zhi-Wei Sun_, Jul 01 2010
-/
theorem conjecture2 (p : ℕ) (hp : p.Prime)
    (h_mod : (p : ℤ) ≡ 3 [ZMOD 20] ∨ (p : ℤ) ≡ 7 [ZMOD 20])
    (x y : ℤ) (h_sq : 2 * (p : ℤ) = x ^ 2 + 5 * y ^ 2) :
    ∑ k ∈ Finset.range p, a k ≡ 2 * x ^ 2 - 2 * (p : ℤ) [ZMOD (p : ℤ) ^ 2] := by
  sorry

end OeisA179524

theorem OeisA179524.conjecture2.disproof : ¬ (type_of% @OeisA179524.conjecture2) := sorry
