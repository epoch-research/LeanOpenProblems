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
# Hardy–Littlewood zeta function conjectures

Two conjectures of Hardy and Littlewood on the zeros of odd order of the function
$\zeta\bigl(\tfrac12 + it\bigr)$ on short intervals $(T, T + H]$ of the critical line, where
$T > 0$ is large and $H = T^{a + \varepsilon}$ with $\varepsilon > 0$ arbitrarily small.
Let $N_0(T)$ be the number of zeros of odd order of $\zeta\bigl(\tfrac12 + it\bigr)$ with
$t \in (0, T]$.

1. For any $\varepsilon > 0$ there exists $T_0 = T_0(\varepsilon) > 0$ such that for
   $T \ge T_0$ and $H = T^{0.25 + \varepsilon}$ the interval $(T, T + H]$ contains a zero of
   odd order of the function $\zeta\bigl(\tfrac12 + it\bigr)$.
2. For any $\varepsilon > 0$ there exist $T_0 = T_0(\varepsilon) > 0$ and
   $c = c(\varepsilon) > 0$ such that for $T \ge T_0$ and $H = T^{0.5 + \varepsilon}$ the
   inequality $N_0(T + H) - N_0(T) \ge cH$ is true.

The first conjecture is open. The second was proved by Selberg (1942), who obtained the stronger
bound $N_0(T + H) - N_0(T) \ge cH \log T$ for $H = T^{0.5 + \varepsilon}$; Karatsuba (1984)
proved the same bound for $H = T^{27/82 + \varepsilon}$.

*References:*
- [Wikipedia: Hardy–Littlewood zeta function conjectures](https://en.wikipedia.org/wiki/Hardy%E2%80%93Littlewood_zeta_function_conjectures)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- G. H. Hardy, J. E. Littlewood, *The zeros of Riemann's zeta-function on the critical line*,
  Math. Z. 10 (1921), 283–317. [doi:10.1007/bf01211614](https://doi.org/10.1007/bf01211614)
- A. Selberg, *On the zeros of Riemann's zeta-function*, Skr. Norske Vid. Akad. Oslo I (1942),
  no. 10, 1–59.
- A. A. Karatsuba, *On the zeros of the function ζ(s) on short intervals of the critical line*,
  Izv. Akad. Nauk SSSR Ser. Mat. 48 (1984), no. 3, 569–584.
-/

namespace HardyLittlewoodZetaFunctionConjectures

open Complex

/-- A real number $t$ is a *zero of odd order* of $\zeta\bigl(\tfrac12 + it\bigr)$ if the order
of vanishing of the Riemann zeta function at the point $\tfrac12 + it$ is odd.

The Riemann zeta function is analytic and not identically zero near every point
$\tfrac12 + it$, so `analyticOrderNatAt riemannZeta (1 / 2 + t * I)` is the genuine multiplicity
of the zero $\tfrac12 + it$ of $\zeta$ (and is `0` when $\zeta(\tfrac12 + it) \ne 0$). Since the
substitution $s = \tfrac12 + it$ is affine, this is the same as the order of $t$ as a zero of the
function $t \mapsto \zeta\bigl(\tfrac12 + it\bigr)$ of a real variable. -/
def IsOddOrderZero (t : ℝ) : Prop :=
  Odd (analyticOrderNatAt riemannZeta (1 / 2 + t * I))

/-- $N_0(T)$: the number of zeros of odd order of $\zeta\bigl(\tfrac12 + it\bigr)$ with
$t \in (0, T]$. -/
noncomputable def oddOrderZeroCount (T : ℝ) : ℕ :=
  {t ∈ Set.Ioc 0 T | IsOddOrderZero t}.ncard

local notation "N₀" => oddOrderZeroCount

/-- **Hardy–Littlewood conjecture 1.**
For any $\varepsilon > 0$ there exists $T_0 = T_0(\varepsilon) > 0$ such that for all
$T \ge T_0$ and $H = T^{0.25 + \varepsilon}$, the interval $(T, T + H]$ contains a zero of odd
order of the function $\zeta\bigl(\tfrac12 + it\bigr)$.

This is open: Karatsuba (1984) proved the analogous statement with the exponent $27/82$ in
place of $0.25$. -/
theorem hardy_littlewood_zeta_function_conjectures.parts.i :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∃ t ∈ Set.Ioc T (T + T ^ (1 / 4 + ε)), IsOddOrderZero t := by
  sorry

end HardyLittlewoodZetaFunctionConjectures

theorem HardyLittlewoodZetaFunctionConjectures.hardy_littlewood_zeta_function_conjectures.parts.i.disproof : ¬ (type_of% @HardyLittlewoodZetaFunctionConjectures.hardy_littlewood_zeta_function_conjectures.parts.i) := sorry
