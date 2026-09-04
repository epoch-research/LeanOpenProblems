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
# Riemann zeta function: the Keating–Snaith moment conjecture

The Keating–Snaith conjecture predicts the asymptotics of the moments of the Riemann zeta
function on the critical line. For real $k \ge 0$ it states that, as $T \to \infty$,
$$\frac{1}{T}\int_0^T \left|\zeta\left(\tfrac{1}{2} + it\right)\right|^{2k} \, dt
  \sim f(k)\, a(k)\, (\log T)^{k^2},$$
where
$$f(k) = \frac{G(1 + k)^2}{G(1 + 2k)}$$
is expressed through the Barnes $G$-function, and
$$a(k) = \prod_{p} \left(1 - \frac{1}{p}\right)^{k^2}
  \sum_{m = 0}^{\infty} \left(\frac{\Gamma(m + k)}{m!\,\Gamma(k)}\right)^2 p^{-m}$$
is an Euler product over the primes. The factor $f(k)$ comes from the moments of the
characteristic polynomial of a random unitary matrix (Keating and Snaith show that
$f(k) = \lim_{N \to \infty} N^{-k^2} \prod_{j=1}^{N} \Gamma(j)\Gamma(j+2k)/\Gamma(j+k)^2$);
the factor $a(k)$ is arithmetic.

Keating and Snaith [KS00] formulated the conjecture for complex $\lambda$ with
$\operatorname{Re} \lambda > -1/2$; here it is stated for real $k \ge 0$. The cases $k = 1$
(Hardy and Littlewood, 1918) and $k = 2$ (Ingham, 1926) are theorems. The cases $k = 3$ and
$k = 4$ recover the constants $42$ and $24024$ conjectured by Conrey–Ghosh and Conrey–Gonek
respectively. All other cases are open.

*References:*
- [Wikipedia: Riemann zeta function](https://en.wikipedia.org/wiki/Riemann_zeta_function)
- [Wikipedia: Keating–Snaith conjecture](https://en.wikipedia.org/wiki/Keating%E2%80%93Snaith_conjecture)
- [Wikipedia: Barnes G-function](https://en.wikipedia.org/wiki/Barnes_G-function)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [KS00] Keating, J. P. and Snaith, N. C. (2000). *Random matrix theory and $\zeta(1/2+it)$*.
  Communications in Mathematical Physics 214 (1): 57–89.
- [HL18] Hardy, G. H. and Littlewood, J. E. (1918). *Contributions to the theory of the Riemann
  zeta-function and the theory of the distribution of primes*. Acta Mathematica 41: 119–196.
- [In26] Ingham, A. E. (1926). *Mean-value theorems in the theory of the Riemann zeta-function*.
  Proceedings of the London Mathematical Society (2) 27: 273–300.
-/

open Real Complex Filter Asymptotics
open scoped Nat

namespace RiemannZetaFunction

/--
The **Barnes $G$-function** on the real line, defined by its Weierstrass product
$$G(1 + z) = (2\pi)^{z/2} \exp\left(-\frac{z + z^2 (1 + \gamma)}{2}\right)
  \prod_{n = 1}^{\infty} \left(1 + \frac{z}{n}\right)^n \exp\left(\frac{z^2}{2n} - z\right),$$
where $\gamma$ is the Euler–Mascheroni constant. The product converges absolutely, so the
`∏'` below is the classical value. It satisfies $G(1) = 1$ and $G(z + 1) = \Gamma(z)\, G(z)$,
so that $G(n + 2) = \prod_{j = 0}^{n} j!$ for $n \in \mathbb{N}$.
-/
noncomputable def barnesG (z : ℝ) : ℝ :=
  (2 * π) ^ ((z - 1) / 2) * rexp (-((z - 1) + (z - 1) ^ 2 * (1 + eulerMascheroniConstant)) / 2) *
    ∏' n : ℕ, (1 + (z - 1) / (n + 1)) ^ (n + 1) * rexp ((z - 1) ^ 2 / (2 * (n + 1)) - (z - 1))

/--
The **random matrix factor** of the Keating–Snaith conjecture:
$$f(k) = \frac{G(1 + k)^2}{G(1 + 2k)},$$
where $G$ is the Barnes $G$-function. For $k \in \mathbb{N}$ one has
$f(k) = \prod_{j = 0}^{k - 1} \frac{j!}{(j + k)!}$, so $f(1) = 1$, $f(2) = \frac{1}{12}$,
$f(3) = \frac{42}{9!}$ and $f(4) = \frac{24024}{16!}$.
-/
noncomputable def randomMatrixFactor (k : ℝ) : ℝ :=
  barnesG (1 + k) ^ 2 / barnesG (1 + 2 * k)

/--
The **arithmetic factor** of the Keating–Snaith conjecture:
$$a(k) = \prod_{p} \left(1 - \frac{1}{p}\right)^{k^2}
  \sum_{m = 0}^{\infty} \left(\frac{\Gamma(m + k)}{m!\,\Gamma(k)}\right)^2 p^{-m},$$
where the product is over all primes $p$. The coefficient
$\frac{\Gamma(m + k)}{m!\,\Gamma(k)} = \frac{k (k + 1) \cdots (k + m - 1)}{m!}$ is the value
$d_k(p^m)$ of the $k$-th generalised divisor function; it is written here with the rising
factorial `ascPochhammer`, which agrees with the Gamma quotient for $k > 0$ and also gives the
correct value ($1$ for $m = 0$ and $0$ for $m \ge 1$) at $k = 0$, where Mathlib's
`Real.Gamma 0 = 0` would give a junk value. Each local factor is $1 + O(p^{-2})$, so the
product converges absolutely.

One has $a(1) = 1$ and $a(2) = \frac{6}{\pi^2}$.
-/
noncomputable def arithmeticFactor (k : ℝ) : ℝ :=
  ∏' p : Nat.Primes, (1 - 1 / (p : ℝ)) ^ (k ^ 2) *
    ∑' m : ℕ, ((ascPochhammer ℝ m).eval k / m !) ^ 2 / (p : ℝ) ^ m

/--
The normalised $2k$-th moment of the Riemann zeta function on the critical line:
$$\frac{1}{T} \int_0^T \left|\zeta\left(\tfrac{1}{2} + it\right)\right|^{2k} \, dt.$$
For $k \ge 0$ the integrand is continuous, so the interval integral is a genuine integral.
-/
noncomputable def zetaMoment (k T : ℝ) : ℝ :=
  (1 / T) * ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k)

/-- $G(1) = 1$. -/
@[category API, AMS 33]
theorem barnesG_one : barnesG 1 = 1 := by
  simp [barnesG]

/-- $f(0) = 1$. -/
@[category API, AMS 11]
theorem randomMatrixFactor_zero : randomMatrixFactor 0 = 1 := by
  simp [randomMatrixFactor, barnesG_one]

/-- $a(0) = 1$: only the $m = 0$ term of each local factor survives. -/
@[category API, AMS 11]
theorem arithmeticFactor_zero : arithmeticFactor 0 = 1 := by
  have h (p : Nat.Primes) :
      ∑' m : ℕ, ((ascPochhammer ℝ m).eval (0 : ℝ) / m !) ^ 2 / (p : ℝ) ^ m = 1 := by
    rw [tsum_eq_single 0]
    · simp
    · intro m hm
      simp [hm]
  simp [arithmeticFactor, h]

/-- $a(1) = 1$: for $k = 1$ each local factor is $(1 - 1/p) \sum_{m \ge 0} p^{-m} = 1$. -/
@[category API, AMS 11]
theorem arithmeticFactor_one : arithmeticFactor 1 = 1 := by
  unfold arithmeticFactor
  refine (tprod_congr fun p => ?_).trans tprod_one
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
  have h0 : (0 : ℝ) < p := by linarith
  have h1 : (0 : ℝ) ≤ 1 / p := by positivity
  have h2 : (1 : ℝ) / p < 1 := by rw [div_lt_one h0]; linarith
  simp only [ascPochhammer_eval_one, one_pow, Real.rpow_one]
  have : ∀ m : ℕ,
      ((m ! : ℝ) / m !) ^ 2 / (p : ℝ) ^ m = (1 / (p : ℝ)) ^ m := by
    intro m
    rw [div_self (by positivity), one_pow, one_div, one_div, inv_pow]
  simp_rw [this, tsum_geometric_of_lt_one h1 h2]
  have h3 : (1 : ℝ) - 1 / p ≠ 0 := by linarith
  rw [mul_inv_cancel₀ h3]

/-- The zeroth moment is $1$. -/
@[category API, AMS 11]
theorem zetaMoment_zero (T : ℝ) (hT : T ≠ 0) : zetaMoment 0 T = 1 := by
  simp [zetaMoment, hT]

/--
**The Keating–Snaith conjecture.** For every real $k \ge 0$, as $T \to \infty$,
$$\frac{1}{T}\int_0^T \left|\zeta\left(\tfrac{1}{2} + it\right)\right|^{2k} \, dt
  \sim f(k)\, a(k)\, (\log T)^{k^2},$$
where $f(k) = \frac{G(1 + k)^2}{G(1 + 2k)}$ is given by the Barnes $G$-function and
$$a(k) = \prod_{p} \left(1 - \frac{1}{p}\right)^{k^2}
  \sum_{m = 0}^{\infty} \left(\frac{\Gamma(m + k)}{m!\,\Gamma(k)}\right)^2 p^{-m}.$$
Since $f(k)\,a(k) > 0$, this is the same as
$\lim_{T \to \infty} (\log T)^{-k^2}\,\frac{1}{T}\int_0^T |\zeta(\tfrac12 + it)|^{2k}\,dt
  = f(k)\,a(k)$, which is how Keating and Snaith phrase it.

Keating and Snaith [KS00] formulated the conjecture for complex $\lambda$ with
$\operatorname{Re} \lambda > -1/2$; here we take real $k \ge 0$. The case $k = 0$ is trivial.
The cases $k = 1$ and $k = 2$ are the theorems of Hardy–Littlewood and Ingham, see
`riemann_zeta_function.variants.one` and `riemann_zeta_function.variants.two`.
-/
@[category research open, AMS 11]
theorem riemann_zeta_function (k : ℝ) (hk : 0 ≤ k) :
    zetaMoment k ~[atTop]
      fun T => randomMatrixFactor k * arithmeticFactor k * Real.log T ^ (k ^ 2) := by
  sorry

/--
Sanity check: the case $k = 0$ of the Keating–Snaith conjecture holds trivially, since both
sides are equal to $1$ for $T \neq 0$.
-/
@[category test, AMS 11]
theorem riemann_zeta_function.variants.zero :
    zetaMoment 0 ~[atTop]
      fun T => randomMatrixFactor 0 * arithmeticFactor 0 * Real.log T ^ ((0 : ℝ) ^ 2) := by
  have h : zetaMoment 0 =ᶠ[atTop]
      fun T => randomMatrixFactor 0 * arithmeticFactor 0 * Real.log T ^ ((0 : ℝ) ^ 2) := by
    filter_upwards [eventually_ne_atTop 0] with T hT
    simp [zetaMoment_zero T hT, randomMatrixFactor_zero, arithmeticFactor_zero]
  exact h.isEquivalent

/--
The case $k = 1$ of the Keating–Snaith conjecture is the theorem of Hardy and Littlewood
[HL18]: as $T \to \infty$,
$$\frac{1}{T}\int_0^T \left|\zeta\left(\tfrac{1}{2} + it\right)\right|^{2} \, dt \sim \log T.$$
Here $f(1)\, a(1) = 1$.
-/
@[category research solved, AMS 11]
theorem riemann_zeta_function.variants.one :
    zetaMoment 1 ~[atTop] fun T => Real.log T := by
  sorry

/--
The case $k = 2$ of the Keating–Snaith conjecture is the theorem of Ingham [In26]: as
$T \to \infty$,
$$\frac{1}{T}\int_0^T \left|\zeta\left(\tfrac{1}{2} + it\right)\right|^{4} \, dt
  \sim \frac{1}{2\pi^2} (\log T)^{4}.$$
Here $f(2)\, a(2) = \frac{1}{12} \cdot \frac{6}{\pi^2} = \frac{1}{2\pi^2}$.
-/
@[category research solved, AMS 11]
theorem riemann_zeta_function.variants.two :
    zetaMoment 2 ~[atTop] fun T => 1 / (2 * π ^ 2) * Real.log T ^ 4 := by
  sorry

end RiemannZetaFunction
