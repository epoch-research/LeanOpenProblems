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

import FormalConjectures.Util.ProblemImports

open Nat Finset Int

/--
A179524: $a(n) = \sum_{k=0}^n (-4)^k \binom{n}{k}^2 \binom{n-k}{k}^2$.
-/
def a (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    (-4 : ℤ) ^ k * (choose n k : ℤ) ^ 2 * (choose (n - k) k : ℤ) ^ 2

/-- Predicate for $n = x^2 + 5y^2$ for $x, y \in \mathbb{Z}$. -/
def is_rep_quadratic_form_5 (n : ℤ) : Prop :=
  ∃ x y : ℤ, n = x^2 + 5 * y^2

/--
Conjectures by Zhi-Wei Sun on congruences for the sum of A179524 terms.

The original conjecture:
"If p is a prime with p=1,9 (mod 20) and p=x^2+5y^2 with x,y integers, then $\sum_{k=0}^{p-1}a(k) \equiv 4x^2-2p \pmod{p^2}$.
If p is a prime with p=3,7 (mod 20) and $2p=x^2+5y^2$ with x,y integers, then $\sum_{k=0}^{p-1}a(k) \equiv 2x^2-2p \pmod{p^2}$.
If p is a prime with p=11,13,17,19 (mod 20), then $\sum_{k=0}^{p-1}w_k \equiv 0 \pmod{p^2}$."
(Assuming $w_k = a(k)$.)
-/
theorem oeis_a179524_sun_conjecture_1 (p : ℕ) (hp : Nat.Prime p) :
  let pZ : ℤ := p
  -- The prime 2 and 5 are excluded by the modulo 20 conditions.
  p ≠ 2 ∧ p ≠ 5 →
  let S : ℤ := (Finset.range p).sum fun k => a k
  ( (pZ ≡ 1 [ZMOD 20] ∨ pZ ≡ 9 [ZMOD 20]) →
    (∀ {x y : ℤ}, (is_rep_quadratic_form_5 pZ → S ≡ 4 * x ^ 2 - 2 * pZ [ZMOD pZ ^ 2])) )
  ∧
  ( (pZ ≡ 3 [ZMOD 20] ∨ pZ ≡ 7 [ZMOD 20]) →
    (∀ {x y : ℤ}, (is_rep_quadratic_form_5 (2 * pZ) → S ≡ 2 * x ^ 2 - 2 * pZ [ZMOD pZ ^ 2])) )
  ∧
  ( (pZ ≡ 11 [ZMOD 20] ∨ pZ ≡ 13 [ZMOD 20] ∨ pZ ≡ 17 [ZMOD 20] ∨ pZ ≡ 19 [ZMOD 20]) →
    S ≡ 0 [ZMOD pZ ^ 2] )
  := by sorry
