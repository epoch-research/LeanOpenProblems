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
# Montgomery's pair correlation conjecture

Montgomery's pair correlation conjecture (1973) asserts that, assuming the Riemann hypothesis,
the pair correlation between pairs of zeros of the Riemann zeta function (normalized to have
unit average spacing) is
$$
  1 - \left(\frac{\sin(\pi u)}{\pi u}\right)^2,
$$
which, as Dyson pointed out to Montgomery, is the pair correlation function of the eigenvalues
of random Hermitian matrices (the Gaussian Unitary Ensemble).

Precisely: write the non-trivial zeros of $\zeta$ as $1/2 + i\gamma$ (this uses the Riemann
hypothesis). For fixed $\alpha \le \beta$, the conjecture states that
$$
  \lim_{T \to \infty}
  \frac{\#\{(\gamma, \gamma') : 0 < \gamma, \gamma' \le T \text{ and }
    2\pi\alpha/\log T \le \gamma - \gamma' \le 2\pi\beta/\log T\}}{\frac{T}{2\pi}\log T}
  = \int_\alpha^\beta \left(1 - \left(\frac{\sin(\pi u)}{\pi u}\right)^2\right)\,\mathrm{d}u
    + \delta(\alpha, \beta),
$$
where pairs of zeros are counted with multiplicity, $\delta(\alpha, \beta) = 1$ if
$0 \in [\alpha, \beta]$ and $\delta(\alpha, \beta) = 0$ otherwise.

*References:*
- [Wikipedia: Montgomery's pair correlation conjecture](https://en.wikipedia.org/wiki/Montgomery%27s_pair_correlation_conjecture)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- H. L. Montgomery, *The pair correlation of zeros of the zeta function*, Analytic number theory
  (Proc. Sympos. Pure Math., Vol. XXIV, St. Louis Univ., St. Louis, Mo., 1972), Amer. Math. Soc.,
  Providence, R.I., 1973, pp. 181–193.
- E. Carneiro, V. Chandee, A. Chirre, M. B. Milinovich, *On Montgomery's pair correlation
  conjecture: a tale of three integrals*, [arXiv:2108.09258](https://arxiv.org/abs/2108.09258).
-/

open Filter

open scoped Real Topology

namespace MontgomerysPairCorrelationConjecture

/-- The multiplicity of the point $1/2 + i\gamma$ of the critical line as a zero of the Riemann
zeta function, i.e. the order of vanishing of $\zeta$ at $1/2 + i\gamma$. It is `0` when
$\zeta(1/2 + i\gamma) \ne 0$.

Under the Riemann hypothesis, the non-trivial zeros of $\zeta$ are exactly the points
$1/2 + i\gamma$ with `zeroMultiplicity γ ≠ 0`, and `zeroMultiplicity γ` is the multiplicity of
that zero. -/
noncomputable def zeroMultiplicity (γ : ℝ) : ℕ :=
  analyticOrderNatAt riemannZeta (1 / 2 + γ * Complex.I)

/-- The set of ordered pairs $(\gamma, \gamma')$ of real numbers with $0 < \gamma, \gamma' \le T$
and
$$
  \frac{2\pi\alpha}{\log T} \le \gamma - \gamma' \le \frac{2\pi\beta}{\log T}.
$$ -/
def pairSet (α β T : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Ioc 0 T ∧ p.2 ∈ Set.Ioc 0 T ∧
    2 * π * α / Real.log T ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ 2 * π * β / Real.log T}

/-- The number of ordered pairs $(\gamma, \gamma')$ of ordinates of zeros $1/2 + i\gamma$,
$1/2 + i\gamma'$ of the Riemann zeta function with $0 < \gamma, \gamma' \le T$ and
$$
  \frac{2\pi\alpha}{\log T} \le \gamma - \gamma' \le \frac{2\pi\beta}{\log T},
$$
where each zero is counted with multiplicity, i.e. each pair $(\gamma, \gamma')$ is weighted by
the product of the multiplicities of $\gamma$ and $\gamma'$. Pairs with $\gamma = \gamma'$ are
included. The sum has finite support since $\zeta$ has only finitely many zeros with ordinate in
$(0, T]$. -/
noncomputable def pairCount (α β T : ℝ) : ℕ :=
  ∑ᶠ p ∈ pairSet α β T, zeroMultiplicity p.1 * zeroMultiplicity p.2

/-- The pair correlation function of the eigenvalues of random Hermitian matrices (the Gaussian
Unitary Ensemble), normalized to unit average spacing:
$$
  1 - \left(\frac{\sin(\pi u)}{\pi u}\right)^2.
$$
It is expressed with `Real.sinc`, so that its value at $u = 0$ is $0$. -/
noncomputable def guePairCorrelation (u : ℝ) : ℝ :=
  1 - Real.sinc (π * u) ^ 2

/-- **Montgomery's pair correlation conjecture.**

Assume the Riemann hypothesis, so that the non-trivial zeros of the Riemann zeta function are
$1/2 + i\gamma$ with $\gamma$ real. Let $\alpha \le \beta$ be fixed. Then
$$
  \lim_{T \to \infty}
  \frac{\#\{(\gamma, \gamma') : 0 < \gamma, \gamma' \le T \text{ and }
    2\pi\alpha/\log T \le \gamma - \gamma' \le 2\pi\beta/\log T\}}{\frac{T}{2\pi}\log T}
  = \int_\alpha^\beta \left(1 - \left(\frac{\sin(\pi u)}{\pi u}\right)^2\right)\,\mathrm{d}u
    + \delta(\alpha, \beta),
$$
where $\gamma, \gamma'$ run over the ordinates of the non-trivial zeros of $\zeta$ counted with
multiplicity, $\delta(\alpha, \beta) = 1$ if $0 \in [\alpha, \beta]$, and
$\delta(\alpha, \beta) = 0$ otherwise. That is, the normalized pair correlation function of the
zeros of $\zeta$ is the pair correlation function $1 - (\sin(\pi u) / (\pi u))^2$ of the
eigenvalues of random Hermitian matrices. -/
@[category research open, AMS 11]
theorem montgomerys_pair_correlation_conjecture (hRH : RiemannHypothesis) (α β : ℝ)
    (hαβ : α ≤ β) :
    Tendsto (fun T : ℝ => (pairCount α β T : ℝ) / (T / (2 * π) * Real.log T)) atTop
      (𝓝 ((∫ u in α..β, guePairCorrelation u) + if 0 ∈ Set.Icc α β then 1 else 0)) := by
  sorry

/-- If $\zeta(1/2 + i\gamma) \ne 0$ then $1/2 + i\gamma$ has multiplicity `0`. -/
@[category API, AMS 11]
theorem zeroMultiplicity_eq_zero_of_ne_zero {γ : ℝ}
    (h : riemannZeta (1 / 2 + γ * Complex.I) ≠ 0) : zeroMultiplicity γ = 0 := by
  unfold zeroMultiplicity analyticOrderNatAt
  rw [analyticOrderAt_eq_zero.mpr (Or.inr h), ENat.toNat_zero]

/-- If $\zeta(1/2 + i\gamma) = 0$ then $1/2 + i\gamma$ has positive multiplicity. -/
@[category API, AMS 11]
theorem zeroMultiplicity_pos_of_eq_zero {γ : ℝ}
    (h : riemannZeta (1 / 2 + γ * Complex.I) = 0) : 0 < zeroMultiplicity γ := by
  have hs : (1 / 2 + γ * Complex.I : ℂ) ≠ 1 := by
    intro hs
    have := congrArg Complex.re hs
    norm_num at this
  have hζ : AnalyticOnNhd ℂ riemannZeta {1}ᶜ :=
    DifferentiableOn.analyticOnNhd
      (fun z hz ↦ (differentiableAt_riemannZeta hz).differentiableWithinAt) isOpen_compl_singleton
  have han : AnalyticAt ℂ riemannZeta (1 / 2 + γ * Complex.I) := hζ _ hs
  have htop : analyticOrderAt riemannZeta (1 / 2 + γ * Complex.I) ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have h2 := hζ.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isConnected_compl_singleton_of_one_lt_rank (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)
        1).isPreconnected hs htop (show (2 : ℂ) ∈ {1}ᶜ by norm_num)
    exact riemannZeta_ne_zero_of_one_lt_re (s := 2) (by norm_num) h2
  unfold zeroMultiplicity analyticOrderNatAt
  rw [Nat.pos_iff_ne_zero, ne_eq, ENat.toNat_eq_zero, not_or, analyticOrderAt_eq_zero, not_or,
    not_not, not_not]
  exact ⟨⟨han, h⟩, htop⟩

/-- There are no pairs to count when `T ≤ 0`. -/
@[category test, AMS 11]
theorem pairSet_eq_empty_of_nonpos {α β T : ℝ} (hT : T ≤ 0) : pairSet α β T = ∅ := by
  ext p
  simp only [pairSet, Set.mem_setOf_eq, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, -⟩
  linarith

/-- There are no pairs of zeros to count when `T ≤ 0`. -/
@[category test, AMS 11]
theorem pairCount_of_nonpos {α β T : ℝ} (hT : T ≤ 0) : pairCount α β T = 0 := by
  rw [pairCount, pairSet_eq_empty_of_nonpos hT, finsum_mem_empty]

/-- If $\beta < \alpha$ and $T > 1$ then no pair $(\gamma, \gamma')$ satisfies the constraints. -/
@[category test, AMS 11]
theorem pairSet_eq_empty_of_lt {α β T : ℝ} (hT : 1 < T) (h : β < α) : pairSet α β T = ∅ := by
  have hlog : 0 < Real.log T := Real.log_pos hT
  ext p
  simp only [pairSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, -, h1, h2⟩
  have := (div_le_div_iff_of_pos_right hlog).mp (h1.trans h2)
  nlinarith [Real.pi_pos]

/-- The GUE pair correlation function vanishes at `0`. -/
@[category test, AMS 11]
theorem guePairCorrelation_zero : guePairCorrelation 0 = 0 := by
  simp [guePairCorrelation]

end MontgomerysPairCorrelationConjecture
