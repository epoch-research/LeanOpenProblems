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
# Extended Riemann Hypothesis

Let $K$ be a number field with ring of integers $\mathcal{O}_K$. The Dedekind zeta function of
$K$ is defined for $\operatorname{Re}(s) > 1$ by
$$\zeta_K(s) = \sum_{I \subseteq \mathcal{O}_K} \frac{1}{N(I)^s},$$
where the sum runs over the nonzero ideals $I$ of $\mathcal{O}_K$ and $N(I)$ is the absolute
norm of $I$. By a theorem of Hecke it extends to a meromorphic function on $\mathbb{C}$ whose
only pole is a simple pole at $s = 1$. The completed zeta function
$$\Lambda_K(s) = |d_K|^{s/2}\,\Gamma_\mathbb{R}(s)^{r_1}\,\Gamma_\mathbb{C}(s)^{r_2}\,\zeta_K(s),
\qquad \Gamma_\mathbb{R}(s) = \pi^{-s/2}\Gamma(s/2), \quad
\Gamma_\mathbb{C}(s) = 2(2\pi)^{-s}\Gamma(s),$$
where $r_1$ (resp. $r_2$) is the number of real (resp. complex) places of $K$, satisfies
$\Lambda_K(s) = \Lambda_K(1 - s)$. The poles of the gamma factors force the *trivial zeros* of
$\zeta_K$: a zero of order $r_1 + r_2$ at each negative even integer, a zero of order $r_2$ at
each negative odd integer, and a zero of order $r_1 + r_2 - 1$ at $s = 0$. All other zeros are
called *nontrivial*; they lie in the critical strip $0 < \operatorname{Re}(s) < 1$.

The **Extended Riemann Hypothesis** (ERH) asks: do the nontrivial zeros of all Dedekind zeta
functions lie on the critical line $1/2 + it$ with real $t$?

Mathlib's `NumberField.dedekindZeta K` is only the Dirichlet series (it returns the junk value
`0` where the series does not converge), so we describe the analytic continuation of $\zeta_K$
by its characteristic properties: a function `ζ : ℂ → ℂ` that is holomorphic on `ℂ \ {1}` and
agrees with the Dirichlet series on the half-plane `Re s > 1`. Such a function exists (Hecke),
and it is unique on `ℂ \ {1}` by the identity theorem (see
`IsDedekindZetaContinuation.eqOn`). Its value at the pole `s = 1` is unconstrained, so the
point `s = 1` is excluded explicitly in the statements below.

*References:*
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia: Generalized Riemann hypothesis, § Extended Riemann hypothesis (ERH)](https://en.wikipedia.org/wiki/Generalized_Riemann_hypothesis%23Extended_Riemann_Hypothesis_%28ERH%29)
- [Wikipedia: Dedekind zeta function](https://en.wikipedia.org/wiki/Dedekind_zeta_function)
- J. Neukirch, *Algebraic Number Theory*, Springer (Grundlehren 322), 1999, Chapter VII, § 5,
  Corollary (5.11).
-/

open NumberField NumberField.InfinitePlace Topology

namespace ExtendedRiemannHypothesis

variable (K : Type*) [Field K] [NumberField K]

/-- `IsDedekindZetaContinuation K ζ` says that `ζ : ℂ → ℂ` is the analytic continuation of the
Dedekind zeta function $\zeta_K$ of the number field `K`: it is holomorphic on `ℂ \ {1}` and it
agrees with the Dirichlet series `NumberField.dedekindZeta K` on the half-plane `Re s > 1`.

Such a function exists (Hecke) and is unique on `ℂ \ {1}` by the identity theorem. Its value
at the pole `s = 1` is not constrained. -/
def IsDedekindZetaContinuation (ζ : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ ζ {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re → ζ s = dedekindZeta K s

/-- The set of trivial zeros of the Dedekind zeta function $\zeta_K$ of the number field `K`
with $r_1$ real places and $r_2$ complex places. These are the zeros forced by the poles of the
gamma factors $\Gamma_\mathbb{R}(s)^{r_1}\,\Gamma_\mathbb{C}(s)^{r_2}$ in the functional
equation:
- $s = -2k$ with $k \geq 1$: a zero of order $r_1 + r_2 \geq 1$;
- $s = -(2k - 1)$ with $k \geq 1$: a zero of order $r_2$, so a zero if and only if $r_2 > 0$;
- $s = 0$: a zero of order $r_1 + r_2 - 1$, so a zero if and only if $r_1 + r_2 \geq 2$, i.e.
  if and only if $K$ is neither $\mathbb{Q}$ nor an imaginary quadratic field.

Every other zero of $\zeta_K$ is called nontrivial. -/
def trivialZeros : Set ℂ :=
  {s | ∃ n : ℕ, s = -2 * (n + 1)} ∪
    {s | 0 < nrComplexPlaces K ∧ ∃ n : ℕ, s = -(2 * n + 1)} ∪
    {s | 2 ≤ nrRealPlaces K + nrComplexPlaces K ∧ s = 0}

/-- The **Extended Riemann Hypothesis**: do the nontrivial zeros of all Dedekind zeta functions
lie on the critical line $1/2 + it$ with real $t$?

That is, is it true that for every number field $K$ and every complex number $s$ with
$\zeta_K(s) = 0$ which is not a trivial zero of $\zeta_K$, one has $\operatorname{Re}(s) = 1/2$?
Here $\zeta_K$ denotes the analytic continuation of the Dedekind zeta function of $K$, and the
pole $s = 1$ is excluded because the value of the continuation there is unconstrained.

For $K = \mathbb{Q}$ this is the Riemann Hypothesis, see `extended_riemann_hypothesis_rat_iff`. -/
@[category research open, AMS 11]
theorem extended_riemann_hypothesis :
    answer(sorry) ↔ ∀ (K : Type*) [Field K] [NumberField K] (ζ : ℂ → ℂ),
      IsDedekindZetaContinuation K ζ →
        ∀ s : ℂ, ζ s = 0 → s ≠ 1 → s ∉ trivialZeros K → s.re = 1 / 2 := by
  sorry

/-- The **Extended Riemann Hypothesis**, critical strip formulation: is it true that for every
number field $K$ and every complex number $s$ with $0 < \operatorname{Re}(s) < 1$ and
$\zeta_K(s) = 0$, one has $\operatorname{Re}(s) = 1/2$?

This is equivalent to `extended_riemann_hypothesis`, since the functional equation shows that
the nontrivial zeros of $\zeta_K$ are exactly its zeros in the critical strip
$0 < \operatorname{Re}(s) < 1$. -/
@[category research open, AMS 11]
theorem extended_riemann_hypothesis.variants.critical_strip :
    answer(sorry) ↔ ∀ (K : Type*) [Field K] [NumberField K] (ζ : ℂ → ℂ),
      IsDedekindZetaContinuation K ζ →
        ∀ s : ℂ, ζ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 := by
  sorry

/-- Two analytic continuations of the Dedekind zeta function of `K` agree on `ℂ \ {1}`. -/
@[category API, AMS 11 30]
theorem IsDedekindZetaContinuation.eqOn {K : Type*} [Field K] [NumberField K] {ζ₁ ζ₂ : ℂ → ℂ}
    (h₁ : IsDedekindZetaContinuation K ζ₁)
    (h₂ : IsDedekindZetaContinuation K ζ₂) : Set.EqOn ζ₁ ζ₂ {1}ᶜ := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (h₁.1.analyticOnNhd hU)
    (h₂.1.analyticOnNhd hU) (isConnected_compl_singleton_of_one_lt_rank ?_ 1).isPreconnected
    (z₀ := 2) (by norm_num) ?_
  · rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  · have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hmem] with s hs
    rw [h₁.2 s hs, h₂.2 s hs]

/-- Every trivial zero of $\zeta_K$ is a non-positive integer. -/
@[category API, AMS 11]
theorem trivialZeros_subset : trivialZeros K ⊆ {s | ∃ n : ℕ, s = -(n : ℂ)} := by
  rintro s ((⟨n, rfl⟩ | ⟨-, n, rfl⟩) | ⟨-, rfl⟩)
  · exact ⟨2 * (n + 1), by push_cast; ring⟩
  · exact ⟨2 * n + 1, by push_cast; ring⟩
  · exact ⟨0, by simp⟩

/-- `0` is a trivial zero of $\zeta_K$ if and only if $r_1 + r_2 \geq 2$. In particular
$\zeta_K(0) \neq 0$ when $K$ is $\mathbb{Q}$ or an imaginary quadratic field. -/
@[category test, AMS 11]
theorem zero_mem_trivialZeros_iff :
    (0 : ℂ) ∈ trivialZeros K ↔ 2 ≤ nrRealPlaces K + nrComplexPlaces K := by
  simp only [trivialZeros, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ((⟨n, hn⟩ | ⟨-, n, hn⟩) | ⟨h, -⟩)
    · norm_cast at hn
    · norm_cast at hn
    · exact h
  · exact fun h ↦ Or.inr ⟨h, trivial⟩

/-- The trivial zeros of the Riemann zeta function $\zeta = \zeta_{\mathbb{Q}}$ are exactly the
negative even integers, as in Mathlib's `RiemannHypothesis`. -/
@[category test, AMS 11]
theorem trivialZeros_rat : trivialZeros ℚ = {s : ℂ | ∃ n : ℕ, s = -2 * (n + 1)} := by
  have h₁ : nrRealPlaces ℚ = 1 := nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ)
  have h₂ : nrComplexPlaces ℚ = 0 :=
    nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ)
  simp [trivialZeros, h₁, h₂]

/-- The Riemann zeta function is the analytic continuation of the Dedekind zeta function
of $\mathbb{Q}$. -/
@[category test, AMS 11]
theorem isDedekindZetaContinuation_riemannZeta : IsDedekindZetaContinuation ℚ riemannZeta := by
  refine ⟨fun s hs ↦ (differentiableAt_riemannZeta hs).differentiableWithinAt,
    fun s hs ↦ ?_⟩
  rw [dedekindZeta, ← LSeries_one_eq_riemannZeta hs]
  refine LSeries_congr (fun {n} hn ↦ ?_) s
  -- For `n ≠ 0` there is exactly one ideal of `𝓞 ℚ` of norm `n`, namely `(n)`.
  suffices h : Nat.card {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} = 1 by simp [h]
  have key : Ideal.absNorm (Ideal.span {(n : 𝓞 ℚ)}) = n := by
    rw [← map_natCast (algebraMap ℤ (𝓞 ℚ)), Ideal.absNorm_span_singleton,
      Algebra.norm_algebraMap_of_basis (Module.Free.chooseBasis ℤ (𝓞 ℚ)),
      ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, Module.finrank_self,
      pow_one, Int.natAbs_natCast]
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨Ideal.span {(n : 𝓞 ℚ)}, key⟩, fun ⟨J, hJ⟩ ↦ ?_⟩
  have hle : Ideal.span {(n : 𝓞 ℚ)} ≤ J := hJ ▸ Ideal.span_singleton_absNorm_le J
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.mpr hle
  have hL1 : Ideal.absNorm L = 1 := by
    have := congr_arg Ideal.absNorm hL
    rw [key, map_mul, hJ] at this
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) (this.symm.trans (mul_one n).symm)
  rw [Ideal.absNorm_eq_one_iff] at hL1
  exact Subtype.ext (show J = Ideal.span {(n : 𝓞 ℚ)} by rw [hL, hL1, Ideal.mul_top])

/-- The case $K = \mathbb{Q}$ of `extended_riemann_hypothesis` is Mathlib's
`RiemannHypothesis`. -/
@[category test, AMS 11]
theorem extended_riemann_hypothesis_rat_iff :
    (∀ ζ : ℂ → ℂ, IsDedekindZetaContinuation ℚ ζ →
      ∀ s : ℂ, ζ s = 0 → s ≠ 1 → s ∉ trivialZeros ℚ → s.re = 1 / 2) ↔ RiemannHypothesis := by
  constructor
  · intro h s hs hs' hs1
    exact h riemannZeta isDedekindZetaContinuation_riemannZeta s hs hs1
      (by rwa [trivialZeros_rat])
  · intro h ζ hζ s hs hs1 hs'
    rw [hζ.eqOn isDedekindZetaContinuation_riemannZeta hs1] at hs
    exact h s hs (by rwa [trivialZeros_rat] at hs') hs1

end ExtendedRiemannHypothesis
