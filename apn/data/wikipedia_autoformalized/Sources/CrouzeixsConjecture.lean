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
# Crouzeix's conjecture

Crouzeix's conjecture (M. Crouzeix, 2004) states that for every $n \times n$ complex matrix $A$
and every complex function $f$ that is analytic in the interior of the field of values
(numerical range) $W(A) = \{x^* A x : \|x\| = 1\}$ of $A$ and continuous up to its boundary,
$$\|f(A)\| \leq 2 \sup_{z \in W(A)} |f(z)|,$$
where $\|\cdot\|$ is the spectral operator $2$-norm. Equivalently, the inequality holds for
every complex polynomial $p$ in place of $f$.

Crouzeix proved the inequality with the constant $11.08$ in place of $2$ (2007), and Crouzeix and
Palencia improved the constant to $1 + \sqrt 2$ (2017). Proofs of the conjecture were announced
in 2026 (Jin; Lorist–Schwenninger).

*References:*
- [Wikipedia, Crouzeix's conjecture](https://en.wikipedia.org/wiki/Crouzeix%27s_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- M. Crouzeix, *Bounds for analytical functions of matrices*, Integral Equations and Operator
  Theory 48 (2004), 461–477. [doi:10.1007/s00020-002-1188-6](https://doi.org/10.1007/s00020-002-1188-6)
- M. Crouzeix, *Numerical range and functional calculus in Hilbert space*, Journal of Functional
  Analysis 244 (2007), 668–690. [doi:10.1016/j.jfa.2006.10.013](https://doi.org/10.1016/j.jfa.2006.10.013)
- M. Crouzeix, C. Palencia, *The numerical range is a $(1+\sqrt2)$-spectral set*, SIAM Journal on
  Matrix Analysis and Applications 38 (2017), 649–655.
  [doi:10.1137/17M1116672](https://doi.org/10.1137/17M1116672)
- E. Lorist, F. Schwenninger, *A solution to Crouzeix's conjecture*,
  [arXiv:2608.03841](https://arxiv.org/abs/2608.03841)
-/

open Filter Matrix Polynomial Topology
open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixsConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **field of values** (or **numerical range**) $W(A) = \{x^* A x : \|x\| = 1\}$ of a square
complex matrix `A`, where `x` ranges over the unit vectors of `EuclideanSpace ℂ n`. Here
`⟪x, A x⟫_ℂ = x^* A x` because Mathlib's inner product is conjugate-linear in its first
argument. -/
def numericalRange (A : Matrix n n ℂ) : Set ℂ :=
  {z | ∃ x : EuclideanSpace ℂ n, ‖x‖ = 1 ∧ ⟪x, toEuclideanLin A x⟫_ℂ = z}

/-- The numerical range of a matrix is compact. -/
@[category API, AMS 15 47]
theorem isCompact_numericalRange (A : Matrix n n ℂ) : IsCompact (numericalRange A) := by
  have : numericalRange A =
      (fun x : EuclideanSpace ℂ n => ⟪x, toEuclideanLin A x⟫_ℂ) '' Metric.sphere 0 1 := by
    ext z
    simp [numericalRange]
  rw [this]
  exact (isCompact_sphere 0 1).image <|
    continuous_id.inner (toEuclideanLin A).continuous_of_finiteDimensional

@[category test, AMS 15 47]
theorem mem_numericalRange_diagonal (d : n → ℂ) (i : n) : d i ∈ numericalRange (diagonal d) :=
  ⟨EuclideanSpace.single i 1, by simp,
    by simp [toEuclideanLin_apply, EuclideanSpace.inner_single_left]⟩

@[category test, AMS 15 47]
theorem numericalRange_one [Nonempty n] : numericalRange (1 : Matrix n n ℂ) = {1} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [toEuclideanLin_apply, one_mulVec, Set.mem_singleton_iff]
    rw [WithLp.toLp_ofLp, inner_self_eq_norm_sq_to_K, hx]
    simp
  · rintro rfl
    exact mem_numericalRange_diagonal (fun _ => 1) (Classical.arbitrary n)

/-- The numerical range of the `1 × 1` matrix `(a)` is `{a}` (and not `{conj a}`). -/
@[category test, AMS 15 47]
theorem numericalRange_fin_one (a : ℂ) : numericalRange !![a] = {a} := by
  have h : toEuclideanLin !![a] = a • LinearMap.id :=
    LinearMap.ext fun v => by ext i; fin_cases i; simp [toEuclideanLin_apply, vecHead]
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp [h, inner_self_eq_norm_sq_to_K, hx]
  · rintro rfl
    exact ⟨EuclideanSpace.single 0 1, by simp, by simp [h, inner_self_eq_norm_sq_to_K]⟩

/-- `IsFunctionalCalculus A f B` says that `B = f(A)`, where `f(A)` is the continuous extension
(Delyon–Delyon, Crouzeix) of the polynomial functional calculus `p ↦ p(A)` to the functions `f`
that are continuous on the numerical range `W(A)` and analytic in its interior: `B` is the limit
of `p k (A)` for a sequence of polynomials `p k` converging uniformly to `f` on `W(A)`. -/
def IsFunctionalCalculus (A : Matrix n n ℂ) (f : ℂ → ℂ) (B : Matrix n n ℂ) : Prop :=
  ∃ p : ℕ → ℂ[X],
    TendstoUniformlyOn (fun k z => (p k).eval z) f atTop (numericalRange A) ∧
      Tendsto (fun k => aeval A (p k)) atTop (𝓝 B)

/-- For a polynomial `p`, `p(A)` is the usual polynomial evaluation `aeval A p`. -/
@[category test, AMS 15 47]
theorem isFunctionalCalculus_aeval (A : Matrix n n ℂ) (p : ℂ[X]) :
    IsFunctionalCalculus A (fun z => p.eval z) (aeval A p) :=
  ⟨fun _ => p, fun _ hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu,
    tendsto_const_nhds⟩

/--
**Crouzeix's conjecture.** Let $A$ be an $n \times n$ complex matrix ($n \geq 1$) and let $f$ be
a complex function that is analytic in the interior of the field of values (numerical range)
$W(A) = \{x^* A x : \|x\| = 1\}$ of $A$ and continuous up to its boundary. Then
$$\|f(A)\| \leq 2 \sup_{z \in W(A)} |f(z)|,$$
where $\|\cdot\|$ is the spectral operator $2$-norm (`Matrix.Norms.L2Operator`) and $f(A)$ is
given by the continuous extension of the polynomial functional calculus (`IsFunctionalCalculus`).
-/
@[category research open, AMS 15 47]
theorem crouzeixs_conjecture [Nonempty n] (A : Matrix n n ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (numericalRange A))
    (hf' : AnalyticOnNhd ℂ f (interior (numericalRange A)))
    (B : Matrix n n ℂ) (hB : IsFunctionalCalculus A f B) :
    ‖B‖ ≤ 2 * sSup ((fun z => ‖f z‖) '' numericalRange A) := by
  sorry

/--
**Crouzeix's conjecture, polynomial form.** For every $n \times n$ complex matrix $A$
($n \geq 1$) and every complex polynomial $p$,
$$\|p(A)\| \leq 2 \sup_{z \in W(A)} |p(z)|,$$
where $W(A)$ is the field of values (numerical range) of $A$ and $\|\cdot\|$ is the spectral
operator $2$-norm (`Matrix.Norms.L2Operator`).
-/
@[category research open, AMS 15 47]
theorem crouzeixs_conjecture.variants.polynomial [Nonempty n] (A : Matrix n n ℂ) (p : ℂ[X]) :
    ‖aeval A p‖ ≤ 2 * sSup ((fun z => ‖p.eval z‖) '' numericalRange A) := by
  sorry

end CrouzeixsConjecture
