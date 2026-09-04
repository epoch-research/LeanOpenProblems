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
# Generalized Riemann hypothesis for the Selberg class

The Selberg class $\mathcal{S}$ is the class of Dirichlet series
$F(s) = \sum_{n \ge 1} a_n n^{-s}$ satisfying Selberg's axioms:

- **Analyticity**: $F$ has a meromorphic continuation to $\mathbb{C}$ whose only possible pole is
  at $s = 1$; more precisely, $(s - 1)^m F(s)$ is an entire function of finite order for some
  integer $m \ge 0$.
- **Ramanujan conjecture**: $a_1 = 1$ and $a_n \ll_\varepsilon n^\varepsilon$ for every
  $\varepsilon > 0$.
- **Functional equation**: there are a gamma factor
  $\gamma(s) = Q^s \prod_{i=1}^k \Gamma(\omega_i s + \mu_i)$, with $Q > 0$, $\omega_i > 0$ real and
  $\mathrm{Re}\,\mu_i \ge 0$, and a root number $\alpha$ with $|\alpha| = 1$, such that
  $\Phi(s) = \gamma(s) F(s)$ satisfies $\Phi(s) = \alpha\,\overline{\Phi(1 - \overline{s})}$.
- **Euler product**: for $\mathrm{Re}\, s > 1$, $F(s) = \prod_p F_p(s)$ with
  $F_p(s) = \exp\left(\sum_{n \ge 1} b_{p^n} p^{-ns}\right)$ and $b_{p^n} = O(p^{n\theta})$ for
  some $\theta < 1/2$.

The zeros of $F$ located at the poles of the gamma factor $\gamma$ (all of which lie in
$\mathrm{Re}\, s \le 0$) are the *trivial zeros*; all other zeros are *nontrivial*. The generalized
Riemann hypothesis for the Selberg class asks whether the nontrivial zeros of every
$F \in \mathcal{S}$ lie on the critical line $\mathrm{Re}\, s = 1/2$.

*References:*
- [Wikipedia, Generalized Riemann hypothesis for Selberg class](https://en.wikipedia.org/wiki/Generalized_Riemann_hypothesis%23Generalized_Riemann_hypothesis_for_Selberg_class)
- [Wikipedia, Selberg class](https://en.wikipedia.org/wiki/Selberg_class)
- A. Selberg, *Old and new conjectures and results about a class of Dirichlet series*,
  Proceedings of the Amalfi Conference on Analytic Number Theory (Maiori, 1989),
  Univ. Salerno, 1992, pp. 367–385.
- J. Kaczorowski, A. Perelli, *The Selberg class: a survey*, Number Theory in Progress, Vol. 2,
  de Gruyter, 1999, pp. 953–992.
-/

namespace GeneralizedRiemannHypothesisForSelbergClass

open Complex Filter Asymptotics
open scoped ComplexConjugate

/-- The data of a gamma factor
$$\gamma(s) = Q^s \prod_{i=1}^{k} \Gamma(\omega_i s + \mu_i),$$
where $Q > 0$ is real, the $\omega_i > 0$ are real, and the $\mu_i$ are complex numbers with
nonnegative real part. The empty product ($k = 0$) is allowed. -/
structure GammaFactor where
  /-- The number $k$ of gamma functions in the product. -/
  k : ℕ
  /-- The positive real number $Q$. -/
  Q : ℝ
  Q_pos : 0 < Q
  /-- The positive real numbers $\omega_i$. -/
  ω : Fin k → ℝ
  ω_pos : ∀ i, 0 < ω i
  /-- The complex numbers $\mu_i$, with nonnegative real part. -/
  μ : Fin k → ℂ
  μ_re_nonneg : ∀ i, 0 ≤ (μ i).re

namespace GammaFactor

/-- The gamma factor as a function: $\gamma(s) = Q^s \prod_{i=1}^{k} \Gamma(\omega_i s + \mu_i)$. -/
noncomputable def toFun (γ : GammaFactor) (s : ℂ) : ℂ :=
  (γ.Q : ℂ) ^ s * ∏ i, Gamma (γ.ω i * s + γ.μ i)

/-- `s` is a pole of the gamma factor $\gamma$, i.e. $\omega_i s + \mu_i$ is a non-positive integer
for some $i$. Since $\mathrm{Re}\,\mu_i \ge 0$, all poles satisfy $\mathrm{Re}\, s \le 0$. -/
def IsPole (γ : GammaFactor) (s : ℂ) : Prop :=
  ∃ (i : Fin γ.k) (n : ℕ), γ.ω i * s + γ.μ i = -n

end GammaFactor

/-- An element of the **Selberg class**: a Dirichlet series $F(s) = \sum_{n \ge 1} a_n n^{-s}$,
given by its coefficients `coeff` and its meromorphic continuation `toFun`, together with a gamma
factor `gamma` and a root number `rootNumber`, satisfying Selberg's axioms (analyticity, Ramanujan
conjecture, functional equation, Euler product).

Since Lean functions `ℂ → ℂ` cannot take the value $\infty$, the continuation `toFun` is only
constrained away from $s = 1$; its value at $s = 1$ is irrelevant. Likewise, the functional
equation is only required at points where neither side involves a pole, which determines the
identity of meromorphic functions by the identity theorem. -/
structure SelbergClass where
  /-- The Dirichlet coefficients $a_n$. -/
  coeff : ℕ → ℂ
  /-- The meromorphic continuation $F(s)$ of the Dirichlet series to the complex plane. -/
  toFun : ℂ → ℂ
  /-- For $\mathrm{Re}\, s > 1$, the Dirichlet series $\sum_{n \ge 1} a_n n^{-s}$ converges
  to $F(s)$. -/
  lSeriesHasSum : ∀ s : ℂ, 1 < s.re → LSeriesHasSum coeff s (toFun s)
  /-- **Analyticity**: for some integer $m \ge 0$, the function $(s - 1)^m F(s)$ agrees away from
  $s = 1$ with an entire function $G$ of finite order, i.e. $|G(s)| \le C \exp(|s|^\rho)$ for
  some constants $C, \rho$. In particular $F$ is meromorphic on $\mathbb{C}$ with its only
  possible pole at $s = 1$. -/
  analyticity : ∃ (m : ℕ) (G : ℂ → ℂ), Differentiable ℂ G ∧
    (∃ C ρ : ℝ, ∀ s, ‖G s‖ ≤ C * Real.exp (‖s‖ ^ ρ)) ∧
    ∀ s, s ≠ 1 → G s = (s - 1) ^ m * toFun s
  /-- **Ramanujan conjecture**, first part: $a_1 = 1$. -/
  coeff_one : coeff 1 = 1
  /-- **Ramanujan conjecture**, second part: $a_n \ll_\varepsilon n^\varepsilon$ for every
  $\varepsilon > 0$. -/
  coeff_isBigO : ∀ ε : ℝ, 0 < ε → coeff =O[atTop] fun n : ℕ => (n : ℝ) ^ ε
  /-- The gamma factor $\gamma(s) = Q^s \prod_{i=1}^{k} \Gamma(\omega_i s + \mu_i)$. -/
  gamma : GammaFactor
  /-- The root number $\alpha$. -/
  rootNumber : ℂ
  /-- The root number satisfies $|\alpha| = 1$. -/
  norm_rootNumber : ‖rootNumber‖ = 1
  /-- **Functional equation**: $\Phi(s) = \alpha\,\overline{\Phi(1 - \overline{s})}$, where
  $\Phi(s) = \gamma(s) F(s)$. The identity is required at every $s$ where both sides are free of
  poles: $s \ne 0$, $s \ne 1$, and neither $s$ nor $1 - \overline{s}$ is a pole of $\gamma$. -/
  functionalEquation : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
    ¬ gamma.IsPole s → ¬ gamma.IsPole (1 - conj s) →
      gamma.toFun s * toFun s = rootNumber * conj (gamma.toFun (1 - conj s) * toFun (1 - conj s))
  /-- **Euler product**: there are coefficients $b_{p^n}$ with $b_{p^n} = O(p^{n\theta})$
  (uniformly in the prime $p$ and $n \ge 1$) for some $\theta < 1/2$, such that for
  $\mathrm{Re}\, s > 1$,
  $$F(s) = \prod_p F_p(s), \qquad F_p(s) = \exp\Big(\sum_{n \ge 1} \frac{b_{p^n}}{p^{ns}}\Big).$$ -/
  eulerProduct : ∃ b : ℕ → ℂ,
    (∃ θ : ℝ, θ < 1 / 2 ∧ ∃ C : ℝ, ∀ p n : ℕ, p.Prime → 1 ≤ n →
      ‖b (p ^ n)‖ ≤ C * (p : ℝ) ^ (n * θ)) ∧
    ∀ s : ℂ, 1 < s.re →
      HasProd (fun p : Nat.Primes =>
        exp (∑' n : ℕ, b (p ^ (n + 1)) / ((p : ℕ) : ℂ) ^ (((n : ℂ) + 1) * s))) (toFun s)

namespace SelbergClass

/-- `s` is a **nontrivial zero** of $F \in \mathcal{S}$: the meromorphic continuation of $F$
vanishes at $s$ (i.e. its order at $s$ is positive, which does not depend on the value of `toFun`
at `s` itself), and $s$ is not a pole of the gamma factor $\gamma$. The zeros of $F$ located at
the poles of $\gamma$ are the trivial zeros. -/
def IsNontrivialZero (F : SelbergClass) (s : ℂ) : Prop :=
  0 < meromorphicOrderAt F.toFun s ∧ ¬ F.gamma.IsPole s

/-- The constant function $1$ (the Dirichlet series with $a_1 = 1$ and $a_n = 0$ for $n \ge 2$)
belongs to the Selberg class, with $k = 0$, $Q = 1$, root number $1$ and $b = 0$. -/
noncomputable def one : SelbergClass where
  coeff := LSeries.delta
  toFun := 1
  lSeriesHasSum s _ := by
    simpa [LSeriesHasSum, funext (LSeries.term_delta s)] using hasSum_ite_eq (1 : ℕ) (1 : ℂ)
  analyticity := ⟨0, 1, differentiable_const 1, ⟨1, 1, fun s => by
    simp [Real.one_le_exp (norm_nonneg s)]⟩, fun s _ => by simp⟩
  coeff_one := by simp [LSeries.delta]
  coeff_isBigO ε hε := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (1 : ℝ) ≤ (n : ℝ) ^ ε := Real.one_le_rpow (by exact_mod_cast hn) hε.le
    simp only [LSeries.delta, one_mul, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans this)]
    split_ifs
    · simpa using this
    · simpa using zero_le_one.trans this
  gamma :=
    ⟨0, 1, one_pos, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  rootNumber := 1
  norm_rootNumber := norm_one
  functionalEquation s _ _ _ _ := by simp [GammaFactor.toFun]
  eulerProduct := ⟨0, ⟨0, by norm_num, 0, fun p n _ _ => by simp⟩, fun s _ => by
    simpa using hasProd_one⟩

end SelbergClass

/-- **Generalized Riemann hypothesis for the Selberg class**: do the nontrivial zeros of all
functions $F$ in the Selberg class lie on the critical line $1/2 + it$, $t \in \mathbb{R}$?
That is, does every nontrivial zero $s$ of every $F \in \mathcal{S}$ satisfy
$\mathrm{Re}\, s = 1/2$? -/
theorem generalized_riemann_hypothesis_for_selberg_class :
    ∀ (F : SelbergClass) (s : ℂ), F.IsNontrivialZero s → s.re = 1 / 2 := by
  sorry

end GeneralizedRiemannHypothesisForSelbergClass

theorem GeneralizedRiemannHypothesisForSelbergClass.generalized_riemann_hypothesis_for_selberg_class.disproof : ¬ (type_of% @GeneralizedRiemannHypothesisForSelbergClass.generalized_riemann_hypothesis_for_selberg_class) := sorry
