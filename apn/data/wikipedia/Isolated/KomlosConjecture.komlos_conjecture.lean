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
# Komlós conjecture

The Komlós conjecture in discrepancy theory: there is a universal constant $K$ such
that for all $n, m$ and all vectors $v_1, \dots, v_n \in \mathbb{R}^m$ with
$\|v_i\|_2 \le 1$, there exist signs $\varepsilon_i \in \{-1, +1\}$ such that
$$\left\|\sum_{i=1}^n \varepsilon_i v_i\right\|_\infty \le K.$$

The best known bound is due to Banaszczyk, who proved that one can always achieve
$O(\sqrt{\log n})$. The Beck–Fiala theorem on the discrepancy of sparse set systems
is a special case (up to scaling), and the conjecture would imply the Beck–Fiala
conjecture that set systems of degree $t$ have discrepancy $O(\sqrt{t})$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Discrepancy_theory#Major_open_problems)
- [W. Banaszczyk, *Balancing vectors and Gaussian measures of n-dimensional convex bodies*,
  Random Structures & Algorithms **12** (1998), 351–360](https://doi.org/10.1002/(SICI)1098-2418(199807)12:4%3C351::AID-RSA3%3E3.0.CO;2-S)
- [J. Spencer, *Six standard deviations suffice*,
  Trans. Amer. Math. Soc. **289** (1985), 679–706](https://doi.org/10.1090/S0002-9947-1985-0784009-0)
-/

namespace KomlosConjecture

/--
**The Komlós conjecture**

There exists a universal constant $K > 0$ such that for all $n, m \in \mathbb{N}$ and
all vectors $v_1, \dots, v_n \in \mathbb{R}^m$ with $\|v_i\|_2 \le 1$ (encoded here as
$\sum_j v_{ij}^2 \le 1$), there exist signs $\varepsilon_i \in \{-1, +1\}$ such that
$\left\|\sum_i \varepsilon_i v_i\right\|_\infty \le K$, i.e.
$\left|\sum_i \varepsilon_i v_{ij}\right| \le K$ for every coordinate $j$.
-/
theorem komlos_conjecture :
    ∃ K : ℝ, 0 < K ∧ ∀ (n m : ℕ) (v : Fin n → Fin m → ℝ),
      (∀ i, ∑ j, (v i j) ^ 2 ≤ 1) →
      ∃ ε : Fin n → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ j, |∑ i, ε i * v i j| ≤ K := by
  sorry

end KomlosConjecture
