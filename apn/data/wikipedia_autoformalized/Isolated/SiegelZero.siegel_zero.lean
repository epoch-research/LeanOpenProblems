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
# Siegel zero

A Landau–Siegel zero (or Siegel zero, or exceptional zero) is a potential counterexample to the
generalized Riemann hypothesis: a real zero $\beta$ of the Dirichlet $L$-function $L(s, \chi_D)$
of a real primitive Dirichlet character $\chi_D$ (the Kronecker symbol of a fundamental
discriminant $D$, a primitive quadratic character modulo $|D|$) that lies very close to $s = 1$,
namely $\beta > 1 - A / \log |D|$, where $A$ is the constant of the classical zero-free region.

Since this depends on the constant $A$, the standard precise form of the question "Do Siegel
zeros exist?" is the "no Siegel zeros" conjecture: writing $\beta_D$ for the largest real zero
of $L(s, \chi_D)$,
$$1 - \beta_D \gg \frac{1}{\log |D|}$$
uniformly over all fundamental discriminants $D$. The expected answer is that Siegel zeros do
not exist. An equivalent formulation is $\frac{L'}{L}(1, \chi_D) = O(\log |D|)$.

*References:*
- [Wikipedia, Siegel zero](https://en.wikipedia.org/wiki/Siegel_zero)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [GS00] A. Granville and H. M. Stark, *ABC implies no "Siegel zeros" for L-functions of
  characters with negative discriminant*, Invent. Math. 139 (2000), 509–523.
- [Ta19] C. Táfula, *On Landau–Siegel zeros and heights of singular moduli*,
  [arXiv:1911.07215](https://arxiv.org/abs/1911.07215).
-/

namespace SiegelZero

/--
**Do Siegel zeros exist?**

The real primitive Dirichlet characters are exactly the Kronecker symbols $\chi_D = (D \mid \cdot)$
of fundamental discriminants $D$; $\chi_D$ is a primitive quadratic character modulo $|D|$, and
$|D| \geq 3$. The "no Siegel zeros" conjecture states that there is an absolute constant $c > 0$
such that for every fundamental discriminant $D$, every real zero $\beta$ of $L(s, \chi_D)$
satisfies
$$\beta \leq 1 - \frac{c}{\log |D|},$$
that is, $1 - \beta_D \gg 1 / \log |D|$ for the largest real zero $\beta_D$ of $L(s, \chi_D)$.
Siegel zeros exist if and only if this conjecture fails: for every $c > 0$ some $L(s, \chi_D)$
has a real zero $\beta > 1 - c / \log |D|$.

The constant $c$ is quantified before $D$; the uniformity in $D$ is the whole content of the
conjecture. The answer is expected to be negative (no Siegel zeros).

Here `q` plays the role of $|D|$ and `χ` the role of $\chi_D$: the primitive quadratic
(`MulChar.IsQuadratic`, i.e. real) Dirichlet characters modulo `q` with `3 ≤ q` are exactly the
$\chi_D$ with $|D| = q$ (the only primitive character modulo `1` is trivial, and there is no
primitive character modulo `2`). The hypothesis `3 ≤ q` also guarantees $\log q > 0$. The bound
is imposed on all real zeros of `χ.LFunction`, which is the meromorphic continuation of
$L(s, \chi)$; the trivial zeros at non-positive integers satisfy it as soon as $c \leq \log 3$,
so this is equivalent to imposing it on the real zeros in the critical strip only.
-/
theorem siegel_zero :
    ¬ ∃ c > (0 : ℝ), ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ.IsQuadratic →
        ∀ β : ℝ, χ.LFunction β = 0 → β ≤ 1 - c / Real.log q := by
  sorry

end SiegelZero

theorem SiegelZero.siegel_zero.disproof : ¬ (type_of% @SiegelZero.siegel_zero) := sorry
