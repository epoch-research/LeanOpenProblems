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
# Skewes's number

Skewes's number is the smallest natural number $x$ for which the prime-counting function
$\pi(x)$ exceeds the logarithmic integral
$$\operatorname{li}(x) = \int_0^x \frac{dt}{\log t}
  = \lim_{\varepsilon \to 0^+} \left(\int_0^{1-\varepsilon} \frac{dt}{\log t}
    + \int_{1+\varepsilon}^x \frac{dt}{\log t}\right)$$
(a Cauchy principal value). Littlewood (1914) proved that such an $x$ exists, and in fact that
$\pi(x) - \operatorname{li}(x)$ changes sign infinitely often. The exact value of Skewes's
number is not known. It is known that $\pi(x) < \operatorname{li}(x)$ for all
$2 \le x \le 10^{19}$ (Büthe), and that there is a crossing $\pi(x) > \operatorname{li}(x)$ below
$e^{727.9513468} \approx 1.397182 \times 10^{316}$ (Saouter–Demichel, Zegowitz). It is not known
whether this crossing is the first one.

The problem from the Wikipedia list of unsolved problems is: *What is the smallest Skewes's
number?*

Since $\operatorname{li}(1) = -\infty$, the comparison $\pi(x) > \operatorname{li}(x)$ is only
meaningful for $x \ge 2$; Büthe defines the Skewes number as the number $x_s \in [2, \infty)$
where the first sign change of $\operatorname{li}(x) - \pi(x)$ occurs. We therefore only
consider natural numbers $x \ge 2$. The `sInf` of the empty set of natural numbers is `0`; by
Littlewood's theorem the set is nonempty, so this default value is never reached.

*References:*
- [Wikipedia, Skewes's number](https://en.wikipedia.org/wiki/Skewes%27s_number)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Logarithmic integral function](https://en.wikipedia.org/wiki/Logarithmic_integral_function)
- [Li14] J. E. Littlewood, *Sur la distribution des nombres premiers*, C. R. Acad. Sci. Paris 158
  (1914), 1869–1872.
- [Bü18] J. Büthe, *An analytic method for bounding ψ(x)*, Math. Comp. 87 (2018), 1991–2009.
  [arXiv:1511.02032](https://arxiv.org/abs/1511.02032)
- [PT16] D. J. Platt and T. S. Trudgian, *On the first sign change of θ(x) − x*, Math. Comp. 85
  (2016), 1539–1547. [arXiv:1407.1914](https://arxiv.org/abs/1407.1914)
- [SD10] Y. Saouter and P. Demichel, *A sharp region where π(x) − li(x) is positive*, Math. Comp.
  79 (2010), 2395–2405. [DOI:10.1090/S0025-5718-10-02351-3](https://doi.org/10.1090/S0025-5718-10-02351-3)
- [Ze10] S. Zegowitz, *On the positive region of π(x) − li(x)*, MSc thesis, University of
  Manchester (2010). http://eprints.ma.man.ac.uk/1547/
-/

open Filter Topology

open scoped Nat.Prime

namespace SkewessNumber

/--
The logarithmic integral
$$\operatorname{li}(x) = \int_0^x \frac{dt}{\log t}
  = \lim_{\varepsilon \to 0^+} \left(\int_0^{1-\varepsilon} \frac{dt}{\log t}
    + \int_{1+\varepsilon}^x \frac{dt}{\log t}\right),$$
where the integral is a Cauchy principal value around the singularity of $1/\log t$ at $t = 1$.
This is $\operatorname{li}$, not the offset logarithmic integral
$\operatorname{Li}(x) = \int_2^x dt/\log t$; they differ by $\operatorname{li}(2) = 1.04516\ldots$.

The limit exists for every real $x > 1$. For $x \le 1$ the value of `li x` is a junk value
(`limUnder` of a non-convergent family), so statements below only use `li x` for `x ≥ 2`.
-/
noncomputable def li (x : ℝ) : ℝ :=
  limUnder (𝓝[>] 0) fun ε : ℝ =>
    (∫ t in (0 : ℝ)..(1 - ε), 1 / Real.log t) + ∫ t in (1 + ε)..x, 1 / Real.log t

/--
The set of natural numbers $x \ge 2$ with $\pi(x) > \operatorname{li}(x)$, where $\pi$ is the
prime-counting function. Skewes's number is the least element of this set. The restriction
$x \ge 2$ excludes the degenerate value $x = 1$, where $\operatorname{li}(1) = -\infty$.
-/
def skewesSet : Set ℕ := {x | 2 ≤ x ∧ li x < π x}

/--
Büthe [Bü18]: $\operatorname{li}(x) - \pi(x) > 0$ for all real $2 \le x \le 10^{19}$. Hence
Skewes's number is larger than $10^{19}$.
-/
theorem skewess_number.variants.buthe (x : ℕ) (hx : 2 ≤ x) (hx' : x ≤ 10 ^ 19) :
    (π x : ℝ) < li x := by
  sorry

end SkewessNumber

theorem SkewessNumber.skewess_number.variants.buthe.disproof : ¬ (type_of% @SkewessNumber.skewess_number.variants.buthe) := sorry
