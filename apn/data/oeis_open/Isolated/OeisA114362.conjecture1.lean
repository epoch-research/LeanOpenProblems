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
# Numerator of $\zeta(4n)/\zeta(2n)^2$ (with $a(0)=2$ instead of $-2$)

The ratio $\zeta(4n)/\zeta(2n)^2$ for $n \ge 1$ is the rational number
$$ Q_n = -2 \frac{B_{4n}}{B_{2n}^2 \binom{4n}{2n}} $$
where $B_k$ is the $k$-th Bernoulli number. The sequence $a(n)$ is the numerator of $Q_n$,
with $a(0)$ defined as $2$.

*References:*
- [A114362](https://oeis.org/A114362)
-/

namespace OeisA114362

open scoped Nat Real
open Filter
open Complex

/--
The primary defining sequence `a`.
Numerator of $\zeta(4n)/\zeta(2n)^2$ (with $a(0)=2$ instead of $-2$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then
    2
  else
    let b4n : ℚ := bernoulli (4 * n)
    let b2n : ℚ := bernoulli (2 * n)
    let binomQn : ℚ := ↑(Nat.choose (4 * n) (2 * n))
    let qN : ℚ := -2 * b4n / (b2n * b2n * binomQn)
    qN.num.natAbs

/--
Conjecture: if an integer $n > 1$ is odd, then $\zeta(2n)/\zeta(n)^2$ is irrational.
Cf. W. Kohnen (link) and my conjecture in A348829. - Thomas Ordowski, Jan 05 2022
-/
theorem conjecture1 (n : ℕ) (hn_gt_one : 1 < n) (hn_odd : Odd n) :
    Irrational ((riemannZeta (2 * n : ℂ) / (riemannZeta (n : ℂ)) ^ 2).re) := by
  sorry

/-- `t n` is used in the second conjecture. -/
noncomputable def t (n : ℕ) : ℝ :=
  (riemannZeta (2 * (n : ℂ))).re / ((riemannZeta (n : ℂ)).re ^ 2)

end OeisA114362
