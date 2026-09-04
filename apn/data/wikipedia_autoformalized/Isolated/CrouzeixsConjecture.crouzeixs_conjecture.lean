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

/-- `IsFunctionalCalculus A f B` says that `B = f(A)`, where `f(A)` is the continuous extension
(Delyon–Delyon, Crouzeix) of the polynomial functional calculus `p ↦ p(A)` to the functions `f`
that are continuous on the numerical range `W(A)` and analytic in its interior: `B` is the limit
of `p k (A)` for a sequence of polynomials `p k` converging uniformly to `f` on `W(A)`. -/
def IsFunctionalCalculus (A : Matrix n n ℂ) (f : ℂ → ℂ) (B : Matrix n n ℂ) : Prop :=
  ∃ p : ℕ → ℂ[X],
    TendstoUniformlyOn (fun k z => (p k).eval z) f atTop (numericalRange A) ∧
      Tendsto (fun k => aeval A (p k)) atTop (𝓝 B)

/--
**Crouzeix's conjecture.** Let $A$ be an $n \times n$ complex matrix ($n \geq 1$) and let $f$ be
a complex function that is analytic in the interior of the field of values (numerical range)
$W(A) = \{x^* A x : \|x\| = 1\}$ of $A$ and continuous up to its boundary. Then
$$\|f(A)\| \leq 2 \sup_{z \in W(A)} |f(z)|,$$
where $\|\cdot\|$ is the spectral operator $2$-norm (`Matrix.Norms.L2Operator`) and $f(A)$ is
given by the continuous extension of the polynomial functional calculus (`IsFunctionalCalculus`).
-/
theorem crouzeixs_conjecture [Nonempty n] (A : Matrix n n ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (numericalRange A))
    (hf' : AnalyticOnNhd ℂ f (interior (numericalRange A)))
    (B : Matrix n n ℂ) (hB : IsFunctionalCalculus A f B) :
    ‖B‖ ≤ 2 * sSup ((fun z => ‖f z‖) '' numericalRange A) := by
  sorry

end CrouzeixsConjecture

theorem CrouzeixsConjecture.crouzeixs_conjecture.disproof : ¬ (type_of% @CrouzeixsConjecture.crouzeixs_conjecture) := sorry
