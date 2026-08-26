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
# Coefficients of $\prod_{k>0} (1 - x^k/k!)$

The sequence $a(n)$ has exponential generating function
$$E(x) = \prod_{k=1}^\infty \left(1 - \frac{x^k}{k!}\right),$$
so that $a(n) = n! [x^n] \prod_{k=1}^n \left(1 - \frac{x^k}{k!}\right)$.

*References:*
- [A185895](https://oeis.org/A185895)
-/

open Polynomial

namespace OeisA185895

/-- The finite polynomial approximation $\prod_{k=1}^n (1 - X^k / k!)$. -/
noncomputable def P (n : ℕ) : Polynomial ℚ :=
  ∏ k ∈ Finset.Icc 1 n, (1 - C (1 / (k.factorial : ℚ)) * X ^ k)

/-- The sequence $a(n) = n! [x^n] \prod_{k=1}^n (1 - x^k / k!)$. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 1
  else (coeff (P n) n * (n.factorial : ℚ)).floor

/-- A natural number $n$ is triangular if $n = k(k+1)/2$ for some $k \in \mathbb{N}$. -/
def IsTriangular (n : ℕ) : Prop := ∃ k : ℕ, n = k * (k + 1) / 2

/-- The $n$-th coefficient of the square of the ordinary generating function $A(x)^2$. -/
noncomputable def c (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), a k * a (n - k)

/--
$a(n)$ differs in sign from $a(n-1)$ if and only if $n$ is a triangular number
(checked up to $n = 1225 = (50 \cdot 51)/2$).
- _Peter Bala_, Mar 17 2022
-/
theorem conjecture1 (n : ℕ) (hn : 0 < n) :
    a n * a (n - 1) < 0 ↔ IsTriangular n := by
  sorry

end OeisA185895
