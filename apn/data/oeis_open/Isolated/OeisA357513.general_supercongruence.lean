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
# Numerator of a sum involving binomial coefficients

$a(n)$ is the numerator of
$\sum_{k = 1}^n \frac{1}{k^3} \binom{n}{k}^2 \binom{n+k}{k}^2$ for $n \ge 1$
with $a(0) = 0$.

*References:*
- [A357513](https://oeis.org/A357513)
-/
namespace OeisA357513

open Nat

/--
A357513: $a(n) = \text{numerator of }
\sum_{k = 1..n} \frac{1}{k^3} \binom{n}{k}^2 \binom{n+k}{k}^2
\text{ for } n \ge 1 \text{ with } a(0) = 0$.
-/
def a (n : ℕ) : ℕ :=
 ∑ k ∈ (Finset.Icc 1 n), ((n.choose k : ℚ) ^ 2 * ((n + k).choose k : ℚ) ^ 2) / k ^ 3 |>.num.natAbs

/--
Let m be a nonnegative integer and set $u(n)$ = the numerator of
$$\sum{k=1}^{n} \frac{1}{k^{2m+1}} \binom{n}{k}^2 \binom{n+k}{k}^2$$
(seems like a typo in the OEIS entry: the sum starts with $k=0$ there. In order
to avoid a division by zero, we replace start the sum at $k=1$.)
-/
noncomputable def u (m : ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ (Finset.Icc 1 n),
    ((n.choose k : ℚ) ^ 2 * ((n + k).choose k : ℚ) ^ 2) / k ^ (2 * m + 1) |>.num.natAbs

/--
We conjecture that $u(p-1) == 0 (mod p^4)$ for all primes $p$,
with a finite number of exceptions that depend on $m$.
-/
theorem general_supercongruence (m : ℕ) : ∃ (exceptions : Finset ℕ), ∀ p, p.Prime →
    p ∉ exceptions → u m (p - 1) = (0 : ZMod (p ^ 4)) := by
  sorry

end OeisA357513

theorem OeisA357513.general_supercongruence.disproof : ¬ (type_of% @OeisA357513.general_supercongruence) := sorry
