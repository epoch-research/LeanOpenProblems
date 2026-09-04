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
# Dirichlet's divisor problem

Let $d(n)$ be the number of divisors of $n$ and let
$$D(x) = \sum_{n \le x} d(n)$$
be the divisor summatory function. Dirichlet proved in 1849 that
$$D(x) = x \log x + (2\gamma - 1) x + \Delta(x), \qquad \Delta(x) = O(\sqrt{x}),$$
where $\gamma$ is the Euler–Mascheroni constant. Dirichlet's divisor problem asks for the
smallest $\theta$ such that $\Delta(x) = O(x^{\theta + \varepsilon})$ for every
$\varepsilon > 0$. Hardy proved in 1916 that $\theta \ge 1/4$, and the best known upper bound
is $\theta \le 131/416$ (Huxley, 2003). It is widely conjectured that the answer is
$\theta = 1/4$.

The Wikipedia list of unsolved problems describes this as a special case of the Piltz divisor
problem, which concerns $D_k(x) = \sum_{n \le x} d_k(n)$ where $d_k(n)$ counts the ways to write
$n$ as a product of $k$ positive integers. In that indexing $D(x) = D_2(x)$, so Dirichlet's
divisor problem is the case $k = 2$.

*References:*
- [Wikipedia, Divisor summatory function](https://en.wikipedia.org/wiki/Divisor_summatory_function%23Dirichlet%27s_divisor_problem)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Ha16] Hardy, G. H., *On Dirichlet's divisor problem*, Proc. London Math. Soc. (2) 15 (1916),
  1–25.
- [Hu03] Huxley, M. N., *Exponential sums and lattice points III*, Proc. London Math. Soc. (3)
  87 (2003), 591–609.
-/

open Filter Real

open scoped ArithmeticFunction.sigma

namespace DirichletsDivisorProblem

/--
The divisor summatory function
$$D(x) = \sum_{n \le x} d(n),$$
where $d(n) = \sigma_0(n)$ is the number of divisors of $n$ and the sum runs over the positive
integers $n \le x$.
-/
noncomputable abbrev D (x : ℝ) : ℕ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, σ 0 n

/--
The error term $\Delta(x)$ in Dirichlet's asymptotic formula
$$D(x) = x \log x + (2\gamma - 1) x + \Delta(x),$$
where $\log$ is the natural logarithm and $\gamma$ is the Euler–Mascheroni constant.
-/
noncomputable abbrev Δ (x : ℝ) : ℝ := D x - x * log x - (2 * eulerMascheroniConstant - 1) * x

/-- The first values of $D(n)$ are $0, 1, 3, 5, 8, 10, 14, 16, 20, 23, 27$ (OEIS A006218). -/
@[category test, AMS 11]
theorem D_ten : D 10 = 27 := by
  simp [D]
  decide

/--
**Dirichlet's divisor problem.** Let $\Delta(x) = D(x) - x \log x - (2\gamma - 1)x$ be the
error term in Dirichlet's asymptotic formula for the divisor summatory function
$D(x) = \sum_{n \le x} d(n)$. The problem asks for the smallest $\theta$ such that
$$\Delta(x) = O\left(x^{\theta + \varepsilon}\right) \quad (x \to \infty)$$
holds for all $\varepsilon > 0$.
Hardy showed that this smallest value is at least $1/4$, and it is conjectured to equal $1/4$.
That is, $\Delta(x) = O(x^{1/4 + \varepsilon})$ for every $\varepsilon > 0$.
-/
@[category research open, AMS 11]
theorem dirichlets_divisor_problem :
    IsLeast {θ : ℝ | ∀ ε > 0, Δ =O[atTop] fun x : ℝ => x ^ (θ + ε)} (1 / 4) := by
  sorry

end DirichletsDivisorProblem
