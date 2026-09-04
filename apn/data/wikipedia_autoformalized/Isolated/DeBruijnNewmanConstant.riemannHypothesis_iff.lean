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
# De Bruijn–Newman constant

Let $\Phi$ be the super-exponentially decaying function
$$\Phi(u) = \sum_{n \ge 1} \left(2\pi^2 n^4 e^{9u} - 3\pi n^2 e^{5u}\right) e^{-\pi n^2 e^{4u}},$$
and, for a real parameter $\lambda$ and a complex variable $z$, let
$$H(\lambda, z) = \int_0^\infty e^{\lambda u^2} \Phi(u) \cos(zu) \, du.$$
Each $H(\lambda, \cdot)$ is an even entire function, and
$H(0, z) = \frac{1}{8} \xi\left(\frac12 + \frac{iz}{2}\right)$ where $\xi$ is the Riemann xi
function.

The **de Bruijn–Newman constant** $\Lambda$ is the unique real number with the property that
$H(\lambda, \cdot)$ has only real zeros if and only if $\lambda \geq \Lambda$. Its existence is
a theorem of Newman (1976), building on de Bruijn (1950), who showed that $H(\lambda, \cdot)$ has
only real zeros for $\lambda \geq 1/2$ and that this property persists when $\lambda$ increases.

The Riemann hypothesis is equivalent to $\Lambda \leq 0$. Rodgers and Tao (2020) proved
Newman's conjecture $\Lambda \geq 0$, so the Riemann hypothesis is equivalent to $\Lambda = 0$.
The best known upper bound is $\Lambda \leq 0.2$ (Platt–Trudgian, 2021).

The problem, as listed in Wikipedia's list of unsolved problems in mathematics, is:
*Find the value of the de Bruijn–Newman constant.*

*References:*
- [Wikipedia, De Bruijn–Newman constant](https://en.wikipedia.org/wiki/De_Bruijn%E2%80%93Newman_constant)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- N. G. de Bruijn,
  [The roots of trigonometric integrals](https://doi.org/10.1215/s0012-7094-50-01720-0),
  Duke Math. J. **17** (1950), 197–226.
- C. M. Newman,
  [Fourier transforms with only real zeros](https://doi.org/10.1090/s0002-9939-1976-0434982-5),
  Proc. Amer. Math. Soc. **61** (1976), 245–251.
- B. Rodgers, T. Tao,
  [The de Bruijn–Newman constant is non-negative](https://arxiv.org/abs/1801.05914),
  Forum Math. Pi **8** (2020), e6.
- A. Dobner,
  [A proof of Newman's conjecture for the extended Selberg class](https://arxiv.org/abs/2005.05142),
  Acta Arith. **201** (2021), 29–62.
- D. H. J. Polymath, [Effective approximation of heat flow evolution of the Riemann ξ function,
  and a new upper bound for the de Bruijn-Newman constant](https://arxiv.org/abs/1904.12438),
  Res. Math. Sci. **6** (2019), 31.
- D. Platt, T. Trudgian,
  [The Riemann hypothesis is true up to $3 \cdot 10^{12}$](https://arxiv.org/abs/2004.09765),
  Bull. Lond. Math. Soc. **53** (2021), 792–797.
-/

open Real

namespace DeBruijnNewmanConstant

/-- The super-exponentially decaying function
$$\Phi(u) = \sum_{n \ge 1} \left(2\pi^2 n^4 e^{9u} - 3\pi n^2 e^{5u}\right) e^{-\pi n^2 e^{4u}}.$$
The series converges absolutely for every real $u$. -/
noncomputable def Φ (u : ℝ) : ℝ :=
  ∑' n : ℕ+,
    (2 * π ^ 2 * (n : ℝ) ^ 4 * rexp (9 * u) - 3 * π * (n : ℝ) ^ 2 * rexp (5 * u)) *
      rexp (-π * (n : ℝ) ^ 2 * rexp (4 * u))

/-- The function $H(\lambda, z) = \int_0^\infty e^{\lambda u^2} \Phi(u) \cos(zu) \, du$ for a real
parameter $\lambda$ (written `t` here, since `λ` is reserved in Lean) and a complex variable $z$.
The integrand decays super-exponentially in $u$, so the integral converges for every $\lambda$
and $z$, and $H(\lambda, \cdot)$ is an entire function. One has
$H(0, z) = \frac{1}{8} \xi\left(\frac12 + \frac{iz}{2}\right)$, where $\xi$ is the Riemann xi
function. -/
noncomputable def H (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ), ((rexp (t * u ^ 2) * Φ u : ℝ) : ℂ) * Complex.cos (z * u)

/-- `HasOnlyRealZeros t` says that every zero of $H(t, \cdot)$ is real, i.e. $H(t, z) = 0$ implies
$\operatorname{Im} z = 0$. -/
def HasOnlyRealZeros (t : ℝ) : Prop :=
  ∀ z : ℂ, H t z = 0 → z.im = 0

/-- `IsDeBruijnNewmanConstant Λ` says that $\Lambda$ has the defining property of the
**de Bruijn–Newman constant**: for every real $\lambda$, the function $H(\lambda, \cdot)$ has only
real zeros if and only if $\lambda \geq \Lambda$. By Newman's theorem exactly one real number has
this property. -/
def IsDeBruijnNewmanConstant (Λ : ℝ) : Prop :=
  ∀ t : ℝ, HasOnlyRealZeros t ↔ Λ ≤ t

/-- The Riemann hypothesis is equivalent to the upper bound $\Lambda \leq 0$ on the
de Bruijn–Newman constant, since $H(0, z) = \frac{1}{8} \xi\left(\frac12 + \frac{iz}{2}\right)$
and the zeros of the Riemann xi function $\xi$ are exactly the non-trivial zeros of $\zeta$. -/
theorem riemannHypothesis_iff {Λ : ℝ} (hΛ : IsDeBruijnNewmanConstant Λ) :
    RiemannHypothesis ↔ Λ ≤ 0 := by
  sorry

end DeBruijnNewmanConstant

theorem DeBruijnNewmanConstant.riemannHypothesis_iff.disproof : ¬ (type_of% @DeBruijnNewmanConstant.riemannHypothesis_iff) := sorry
