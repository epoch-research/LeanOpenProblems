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
# Piltz divisor problem

Let $d_k(n)$ be the number of ways to write $n$ as an ordered product of $k$ positive integers,
and let $D_k(x) = \sum_{n \le x} d_k(n)$ be its summatory function. For every integer $k \ge 2$
one has
$$D_k(x) = x P_k(\log x) + \Delta_k(x),$$
where $P_k$ is a polynomial of degree $k - 1$ (the residue of $\zeta(s)^k x^{s - 1} / s$ at
$s = 1$) and $\Delta_k(x) = O(x^{1 - 1/k} \log^{k - 2} x)$. The polynomial $P_k$ is uniquely
determined by the requirement $\Delta_k(x) = o(x)$.

The Piltz divisor problem asks for the order $\alpha_k$ of the error term, defined as the
smallest $\alpha$ such that $\Delta_k(x) = O(x^{\alpha + \varepsilon})$ for every
$\varepsilon > 0$. Titchmarsh conjectured that
$$\alpha_k = \frac{k - 1}{2k}.$$
The lower bound $\alpha_k \ge (k - 1) / (2k)$ is classical, so the open part of the conjecture
is the upper bound $\Delta_k(x) = O(x^{(k - 1) / (2k) + \varepsilon})$ for every
$\varepsilon > 0$. The case $k = 2$ is the Dirichlet divisor problem.

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Divisor summatory function](https://en.wikipedia.org/wiki/Divisor_summatory_function%23Piltz_divisor_problem)
- [Ti86] Titchmarsh, E. C., *The Theory of the Riemann Zeta-Function*, 2nd ed., revised by
  D. R. Heath-Brown, Oxford University Press (1986), Chapter XII.
- [Iv03] Ivić, A., *The Riemann Zeta-Function: Theory and Applications*, Dover (2003),
  Chapter 13.
-/

open ArithmeticFunction Asymptotics Filter
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma

namespace PiltzDivisorProblem

/--
The Piltz divisor summatory function
$$D_k(x) = \sum_{n \le x} d_k(n),$$
where $d_k(n) = (\zeta * \cdots * \zeta)(n)$ (the $k$-fold Dirichlet convolution of the constant
function $1$) is the number of ways to write $n$ as an ordered product of $k$ positive integers.
-/
noncomputable def D (k : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ζ ^ k) n : ℝ)

/--
The error term $\Delta_k(x) = D_k(x) - x P(\log x)$ of $D_k$ with respect to a candidate main
term polynomial $P$.
-/
noncomputable def Δ (k : ℕ) (P : Polynomial ℝ) (x : ℝ) : ℝ :=
  D k x - x * P.eval (Real.log x)

/--
`IsMainTermPolynomial k P` says that $P$ is the polynomial $P_k$ of the Piltz divisor problem,
i.e. that $D_k(x) = x P(\log x) + o(x)$.

This condition determines $P$ uniquely: if $P$ and $Q$ both satisfy it, then
$(P - Q)(\log x) \to 0$ as $x \to \infty$, so $P = Q$. For $k \ge 2$ such a polynomial exists
(see `piltz_divisor_problem.variants.elementary_bound`); it has degree $k - 1$ and is given by
the residue of $\zeta(s)^k x^{s - 1} / s$ at $s = 1$.
-/
def IsMainTermPolynomial (k : ℕ) (P : Polynomial ℝ) : Prop :=
  Δ k P =o[atTop] fun x => x

/--
The order $\alpha_k$ of the error term $\Delta_k$: the infimum of the exponents $\alpha$ such
that $\Delta_k(x) = O(x^{\alpha + \varepsilon})$ for every $\varepsilon > 0$.

The set of such exponents is closed and upward closed, so the infimum is attained and
$\alpha_k$ is the smallest such exponent.
-/
noncomputable def α (k : ℕ) (P : Polynomial ℝ) : ℝ :=
  sInf {a : ℝ | ∀ ε > 0, Δ k P =O[atTop] fun x => x ^ (a + ε)}

/--
The classical lower bound $\alpha_k \ge (k - 1) / (2k)$, i.e.
$\Delta_k(x) \ne o(x^{(k - 1) / (2k)})$. Hardy proved this for $k = 2$ in 1916; for general $k$
see [Ti86], Chapter XII, and [Iv03], Chapter 13.
-/
theorem piltz_divisor_problem.variants.lower_bound (k : ℕ) (hk : 2 ≤ k) (P : Polynomial ℝ)
    (hP : IsMainTermPolynomial k P) :
    ((k : ℝ) - 1) / (2 * k) ≤ α k P := by
  sorry

end PiltzDivisorProblem

theorem PiltzDivisorProblem.piltz_divisor_problem.variants.lower_bound.disproof : ¬ (type_of% @PiltzDivisorProblem.piltz_divisor_problem.variants.lower_bound) := sorry
