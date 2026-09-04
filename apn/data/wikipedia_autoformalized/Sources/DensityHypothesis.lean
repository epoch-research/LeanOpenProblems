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
# The density hypothesis for zeros of the Riemann zeta function

For $\sigma, T \in \mathbb{R}$ let
$$N(\sigma, T) = \#\{\rho \in \mathbb{C} : \zeta(\rho) = 0,\ \operatorname{Re}\rho \ge \sigma,\
  0 < \operatorname{Im}\rho \le T\}$$
be the number of zeros of the Riemann zeta function in the rectangle
$\sigma \le \operatorname{Re} s$, $0 < \operatorname{Im} s \le T$. For $\sigma \ge 1/2$ these
are non-trivial zeros in the critical strip, and there are finitely many of them.

The **density hypothesis** asserts that for every $\sigma$ with $\frac12 \le \sigma \le 1$
and every $\varepsilon > 0$,
$$N(\sigma, T) = O_{\sigma, \varepsilon}\left(T^{2(1 - \sigma) + \varepsilon}\right)
\qquad (T \to \infty).$$
It is implied by the Riemann Hypothesis and by the Lindelöf Hypothesis, and it is the
zero-density statement studied by Bombieri and A. I. Vinogradov in 1965 in connection with the
Bombieri–Vinogradov theorem. It remains open.

Some authors count the zeros with $|\operatorname{Im}\rho| \le T$ instead. By the symmetry
$\zeta(\bar s) = \overline{\zeta(s)}$ and the absence of zeros with $\operatorname{Re}\rho \ge 1/2$
on the real axis, this exactly doubles $N(\sigma, T)$ and does not affect the hypothesis.
Likewise, counting zeros with multiplicity gives an equivalent statement, since each zero
with $0 < \operatorname{Im}\rho \le T$ has multiplicity $O(\log T)$.

*References:*
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia: Bombieri–Vinogradov theorem](https://en.wikipedia.org/wiki/Bombieri%E2%80%93Vinogradov_theorem)
- [Te15] G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, 3rd ed.,
  Graduate Studies in Mathematics 163, American Mathematical Society, 2015, Chapter II.3.
- [Iv85] A. Ivić, *The Riemann Zeta-Function: Theory and Applications*, Wiley, 1985,
  Chapter 11.
-/

open Filter Asymptotics

namespace DensityHypothesis

/-- The zero-counting function $N(\sigma, T)$: the number of zeros $\rho$ of the Riemann zeta
function with $\operatorname{Re}\rho \ge \sigma$ and $0 < \operatorname{Im}\rho \le T$.

Here `riemannZeta` is Mathlib's meromorphic continuation of $\zeta$. The zeros in such a
rectangle form a finite set, so `Set.ncard` is the genuine count. Every trivial zero
$-2, -4, \ldots$ and the point $s = 1$ have imaginary part $0$, so they are never counted. -/
noncomputable def N (σ T : ℝ) : ℕ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T}.ncard

/-- No zeros are counted when $T \le 0$. -/
@[category test, AMS 11]
theorem N_eq_zero_of_nonpos (σ : ℝ) {T : ℝ} (hT : T ≤ 0) : N σ T = 0 := by
  have : {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T} = ∅ :=
    Set.eq_empty_of_forall_notMem fun ρ ⟨_, _, h₁, h₂⟩ => by linarith
  rw [N, this, Set.ncard_empty]

/-- No zeros are counted when $\sigma \ge 1$, since $\zeta(s) \ne 0$ for
$\operatorname{Re} s \ge 1$. -/
@[category test, AMS 11]
theorem N_eq_zero_of_one_le {σ : ℝ} (hσ : 1 ≤ σ) (T : ℝ) : N σ T = 0 := by
  have : {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T} = ∅ :=
    Set.eq_empty_of_forall_notMem fun ρ ⟨h₀, h₁, _, _⟩ =>
      riemannZeta_ne_zero_of_one_le_re (hσ.trans h₁) h₀
  rw [N, this, Set.ncard_empty]

/-- Under the Riemann Hypothesis, $N(\sigma, T) = 0$ for every $\sigma > \frac12$; in particular
the Riemann Hypothesis implies the density hypothesis. -/
@[category test, AMS 11]
theorem N_eq_zero_of_riemannHypothesis (h : RiemannHypothesis) {σ : ℝ} (hσ : 1 / 2 < σ)
    (T : ℝ) : N σ T = 0 := by
  have : {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun ρ ⟨h₀, h₁, h₂, _⟩ => ?_
    have h₃ : ρ.re = 1 / 2 := h ρ h₀ ?_ ?_
    · linarith
    · rintro ⟨n, rfl⟩
      simp at h₂
    · rintro rfl
      simp at h₂
  rw [N, this, Set.ncard_empty]

/-- **The density hypothesis** for zeros of the Riemann zeta function: for every
$\frac12 \le \sigma \le 1$ and every $\varepsilon > 0$,
$$N(\sigma, T) = O_{\sigma, \varepsilon}\left(T^{2(1 - \sigma) + \varepsilon}\right)
\qquad (T \to \infty),$$
where $N(\sigma, T)$ is the number of zeros $\rho$ of $\zeta$ with
$\operatorname{Re}\rho \ge \sigma$ and $0 < \operatorname{Im}\rho \le T$. The implied constant
may depend on $\sigma$ and $\varepsilon$. -/
@[category research open, AMS 11]
theorem density_hypothesis (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2) 1) (ε : ℝ) (hε : 0 < ε) :
    (fun T : ℝ => (N σ T : ℝ)) =O[atTop] fun T => T ^ (2 * (1 - σ) + ε) := by
  sorry

/-- The density hypothesis in the form with a constant uniform in $\sigma$: for every
$\varepsilon > 0$ there is a constant $C = C(\varepsilon)$ such that
$$N(\sigma, T) \le C \, T^{2(1-\sigma)+\varepsilon}$$
for all $\frac12 \le \sigma \le 1$ and all $T \ge 2$.

This is equivalent to `density_hypothesis`, since $N(\sigma, T)$ is non-increasing in $\sigma$
and $T \mapsto T^{2(1-\sigma)+\varepsilon}$ is increasing in the exponent for $T \ge 2$. -/
@[category research open, AMS 11]
theorem density_hypothesis.variants.uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ T : ℝ, 2 ≤ T →
      (N σ T : ℝ) ≤ C * T ^ (2 * (1 - σ) + ε) := by
  sorry

end DensityHypothesis
