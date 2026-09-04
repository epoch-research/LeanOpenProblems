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
# Selberg's 1/4 conjecture

Selberg's $1/4$ conjecture (also called Selberg's eigenvalue conjecture, 1965) states that the
eigenvalues of the Laplace operator on Maass wave forms of congruence subgroups are at least $1/4$.

More precisely, let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ be a congruence subgroup and let
$\Delta = -y^2 (\partial_x^2 + \partial_y^2)$ be the hyperbolic Laplacian on the upper half plane
$\mathbb{H}$. A *Maass cusp form* for $\Gamma$ with eigenvalue $\lambda$ is a smooth function
$f : \mathbb{H} \to \mathbb{C}$ which is $\Gamma$-invariant, satisfies $\Delta f = \lambda f$,
has moderate growth at every cusp, and whose constant Fourier coefficient vanishes at every cusp.
The conjecture asserts that $\lambda \ge 1/4$ for every nonzero Maass cusp form $f$ for $\Gamma$.
Equivalently, the smallest nonzero eigenvalue $\lambda_1(\Gamma \backslash \mathbb{H})$ of the
Laplacian on $L^2(\Gamma \backslash \mathbb{H})$ is at least $1/4$: for congruence subgroups the
residual spectrum consists only of the eigenvalue $0$ of the constant functions, so the remaining
discrete spectrum comes from cusp forms.

Selberg proved $\lambda \ge 3/16$. The best known bound is $\lambda \ge 975/4096$, due to Kim and
Sarnak (2003).

*References:*
- [Wikipedia, *Selberg's 1/4 conjecture*](https://en.wikipedia.org/wiki/Selberg%27s_1/4_conjecture)
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Encyclopedia of Mathematics, *Selberg conjecture*](https://encyclopediaofmath.org/wiki/Selberg_conjecture)
- A. Selberg, *On the estimation of Fourier coefficients of modular forms*, Proc. Sympos. Pure
  Math. VIII (1965), 1–15.
- H. Kim and P. Sarnak, *Functoriality for the exterior square of $GL_4$ and the symmetric fourth
  of $GL_2$*, Appendix 2, J. Amer. Math. Soc. 16 (2003), 139–183.
-/

namespace Selbergs14Conjecture

open UpperHalfPlane CongruenceSubgroup Asymptotics
open scoped MatrixGroups ContDiff Laplacian

local notation "ℍₒ" => UpperHalfPlane.upperHalfPlaneSet

/-- `IsMaassCuspForm Γ f μ` says that `f : ℍ → ℂ` is a **Maass cusp form** (of weight $0$) for
the subgroup `Γ` of `SL(2, ℤ)` with Laplace eigenvalue `μ`. That is:
- `f` is smooth (as a function of the two real variables $x, y$ where $z = x + iy$);
- `f` is `Γ`-invariant: $f(\gamma z) = f(z)$ for all $\gamma \in \Gamma$;
- `f` is an eigenfunction of the hyperbolic Laplacian
  $\Delta = -y^2 (\partial_x^2 + \partial_y^2)$ with eigenvalue `μ`;
- `f` has at most polynomial growth at every cusp of `Γ`;
- the constant Fourier coefficient of `f` vanishes at every cusp of `Γ`.

Smoothness and the Laplacian are expressed through the extension `↑ₕf = f ∘ ofComplex : ℂ → ℂ`
of `f`, whose values outside `ℍ` are irrelevant since only points of `ℍ` are considered and the
Laplacian is local; `Δ` is the Euclidean Laplacian $\partial_x^2 + \partial_y^2$ on `ℂ ≅ ℝ²`.

The cusps of `Γ` are the `Γ`-orbits of the rational points of the boundary of `ℍ`, all of which
are of the form `σ • ∞` with `σ ∈ SL(2, ℤ)`. A condition at the cusp `σ • ∞` is a condition on
the function `z ↦ f (σ • z)` as `Im z → ∞`. If `σ * T ^ n * σ⁻¹ ∈ Γ` with `0 < n`, where
`T : z ↦ z + 1`, this function is periodic with period `n`, and its constant Fourier coefficient
at height `y` is `(1 / n) ∫₀ⁿ f (σ • (x + iy)) dx`. For a congruence subgroup such an `n` exists
at every cusp, so the cuspidality condition is never vacuous.

The eigenvalue `μ` is taken to be real: the Laplace eigenvalues of Maass cusp forms are always
real (and nonnegative), since `Δ` is symmetric and nonnegative on $L^2(\Gamma \backslash
\mathbb{H})$. -/
structure IsMaassCuspForm (Γ : Subgroup SL(2, ℤ)) (f : ℍ → ℂ) (μ : ℝ) : Prop where
  /-- `f` is smooth on `ℍ`, in the real sense. -/
  smooth : ContDiffOn ℝ ∞ (↑ₕf) ℍₒ
  /-- `f` is invariant under `Γ`. -/
  invariant : ∀ γ ∈ Γ, ∀ z : ℍ, f (γ • z) = f z
  /-- `f` is an eigenfunction of the hyperbolic Laplacian `-y² (∂ₓ² + ∂ᵧ²)` with eigenvalue `μ`. -/
  eigen : ∀ z : ℍ, -(z.im : ℂ) ^ 2 * Δ (↑ₕf) z = μ * f z
  /-- `f` has at most polynomial growth at every cusp of `Γ`. -/
  moderateGrowth : ∀ σ : SL(2, ℤ),
    ∃ N : ℕ, (fun z : ℍ => f (σ • z)) =O[atImInfty] fun z => z.im ^ N
  /-- The constant Fourier coefficient of `f` vanishes at every cusp of `Γ`. -/
  cuspidal : ∀ σ : SL(2, ℤ), ∀ n : ℕ, 0 < n → σ * ModularGroup.T ^ n * σ⁻¹ ∈ Γ →
    ∀ z : ℍ, ∫ x in (0 : ℝ)..n, f (σ • (x +ᵥ z)) = 0

/-- The zero function is a Maass cusp form for every subgroup and every eigenvalue. This is why
`selbergs_1_4_conjecture` assumes `f ≠ 0`. -/
@[category test, AMS 11]
theorem isMaassCuspForm_zero (Γ : Subgroup SL(2, ℤ)) (μ : ℝ) : IsMaassCuspForm Γ 0 μ where
  smooth := contDiffOn_const
  invariant _ _ _ := rfl
  eigen z := by
    have h : Δ (0 : ℂ → ℂ) = 0 := by
      rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
      have h := iteratedFDeriv_zero_fun (𝕜 := ℝ) (E := ℂ) (F := ℂ) (n := 2)
      ext x
      simp only [Pi.zero_def] at h ⊢
      simp [h]
    simp [Pi.zero_comp, h]
  moderateGrowth _ := ⟨0, isBigO_zero _ _⟩
  cuspidal _ _ _ _ _ := by simp

/-- A nonzero constant function is not a Maass cusp form for a congruence subgroup: its constant
term at the cusp `∞` does not vanish. In particular the trivial eigenvalue `0` of the constant
functions is excluded from `selbergs_1_4_conjecture`. -/
@[category test, AMS 11]
theorem not_isMaassCuspForm_const {Γ : Subgroup SL(2, ℤ)} (hΓ : IsCongruenceSubgroup Γ)
    {c : ℂ} (hc : c ≠ 0) (μ : ℝ) : ¬ IsMaassCuspForm Γ (fun _ ↦ c) μ := by
  intro hf
  obtain ⟨N, hN, hΓN⟩ := hΓ
  have hT : (1 : SL(2, ℤ)) * ModularGroup.T ^ N * 1⁻¹ ∈ Γ := by
    simpa using hΓN (ModularGroup_T_pow_mem_Gamma N N dvd_rfl)
  have := hf.cuspidal 1 N (Nat.pos_of_ne_zero hN) hT ⟨Complex.I, by simp⟩
  simp [hc, hN] at this

/-- **Selberg's 1/4 conjecture**: the eigenvalues of the Laplace operator on Maass wave forms of
congruence subgroups are at least $1/4$.

That is, if `Γ` is a congruence subgroup of `SL(2, ℤ)` and `f ≠ 0` is a Maass cusp form for `Γ`
with Laplace eigenvalue `μ`, then `μ ≥ 1/4`. In other words, the smallest positive eigenvalue
$\lambda_1(\Gamma \backslash \mathbb{H})$ of the hyperbolic Laplacian
$-y^2 (\partial_x^2 + \partial_y^2)$ satisfies $\lambda_1 \ge 1/4$: there are no exceptional
eigenvalues in $(0, 1/4)$. The eigenvalue $0$ of the constant functions is excluded, since
constant functions are not cuspidal. -/
@[category research open, AMS 11]
theorem selbergs_1_4_conjecture (Γ : Subgroup SL(2, ℤ)) (hΓ : IsCongruenceSubgroup Γ)
    (f : ℍ → ℂ) (μ : ℝ) (hf : IsMaassCuspForm Γ f μ) (hf₀ : f ≠ 0) : 1 / 4 ≤ μ := by
  sorry

end Selbergs14Conjecture
