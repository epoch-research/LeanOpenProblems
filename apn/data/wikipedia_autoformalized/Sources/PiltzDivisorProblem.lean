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

/-- For $k = 2$, $D_2$ is the classical divisor summatory function $\sum_{n \le x} d(n)$. -/
@[category test, AMS 11]
theorem D_two (x : ℝ) : D 2 x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (σ 0 n : ℝ) := by
  simp only [D, sq, ← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]

/-- $D_k(x) = 0$ for $x < 1$. -/
@[category test, AMS 11]
theorem D_eq_zero_of_lt_one {k : ℕ} {x : ℝ} (hx : x < 1) : D k x = 0 := by
  simp [D, Nat.floor_eq_zero.mpr hx]

/--
**Piltz divisor problem** (Titchmarsh's conjecture). For every integer $k \ge 2$, writing
$D_k(x) = x P_k(\log x) + \Delta_k(x)$ with $P_k$ the polynomial (of degree $k - 1$) for which
$\Delta_k(x) = o(x)$, the order
$$\alpha_k = \inf\{\alpha : \Delta_k(x) = O(x^{\alpha + \varepsilon}) \text{ for every }
\varepsilon > 0\}$$
of the error term satisfies
$$\alpha_k = \frac{k - 1}{2k}.$$
-/
@[category research open, AMS 11]
theorem piltz_divisor_problem (k : ℕ) (hk : 2 ≤ k) (P : Polynomial ℝ)
    (hP : IsMainTermPolynomial k P) :
    α k P = ((k : ℝ) - 1) / (2 * k) := by
  sorry

/--
The open content of the Piltz divisor problem: for every integer $k \ge 2$ and every
$\varepsilon > 0$,
$$\Delta_k(x) = O\left(x^{(k - 1) / (2k) + \varepsilon}\right).$$
-/
@[category research open, AMS 11]
theorem piltz_divisor_problem.variants.upper_bound (k : ℕ) (hk : 2 ≤ k) (P : Polynomial ℝ)
    (hP : IsMainTermPolynomial k P) (ε : ℝ) (hε : 0 < ε) :
    Δ k P =O[atTop] fun x => x ^ (((k : ℝ) - 1) / (2 * k) + ε) := by
  sorry

/--
The classical lower bound $\alpha_k \ge (k - 1) / (2k)$, i.e.
$\Delta_k(x) \ne o(x^{(k - 1) / (2k)})$. Hardy proved this for $k = 2$ in 1916; for general $k$
see [Ti86], Chapter XII, and [Iv03], Chapter 13.
-/
@[category research solved, AMS 11]
theorem piltz_divisor_problem.variants.lower_bound (k : ℕ) (hk : 2 ≤ k) (P : Polynomial ℝ)
    (hP : IsMainTermPolynomial k P) :
    ((k : ℝ) - 1) / (2 * k) ≤ α k P := by
  sorry

/--
The elementary estimate: for every integer $k \ge 2$ there is a polynomial $P_k$ with
$$D_k(x) = x P_k(\log x) + O\left(x^{1 - 1/k} \log^{k - 2} x\right).$$
In particular the main term polynomial $P_k$ exists, so the hypothesis `IsMainTermPolynomial`
of `piltz_divisor_problem` is satisfiable.
-/
@[category research solved, AMS 11]
theorem piltz_divisor_problem.variants.elementary_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ P : Polynomial ℝ, IsMainTermPolynomial k P ∧
      Δ k P =O[atTop] fun x => x ^ (1 - 1 / (k : ℝ)) * Real.log x ^ (k - 2) := by
  sorry

end PiltzDivisorProblem
