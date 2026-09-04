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
# Hilbert–Pólya conjecture

The Hilbert–Pólya conjecture states that the nontrivial zeros of the Riemann zeta function
correspond to eigenvalues of a self-adjoint operator. In Pólya's formulation, a nontrivial zero
$\rho = \tfrac12 + i\mu$ corresponds to the eigenvalue $\mu$.

Such an operator must be unbounded, because the imaginary parts of the zeros are unbounded. It is
therefore modelled by a partially defined linear map `A : H →ₗ.[ℂ] H` (`LinearPMap`), and
self-adjointness is Mathlib's `IsSelfAdjoint` for `LinearPMap`, i.e. `A† = A`. A complex number
$\mu$ is an eigenvalue of `A` if `A x = μ • x` for some nonzero `x` in the domain of `A`.

Since the eigenvalues of a self-adjoint operator are real, the statement implies the Riemann
Hypothesis (see `hilbert_polya_conjecture_implies_riemannHypothesis`). Conversely, under the
Riemann Hypothesis it is witnessed by a diagonal operator on $\ell^2$ whose diagonal entries are
the imaginary parts of the nontrivial zeros. The informal statement does not specify the operator
or a relation between the order of a zero and the dimension of the corresponding eigenspace, and
the formalisation does not impose any.

*References:*
- [Wikipedia: Hilbert–Pólya conjecture](https://en.wikipedia.org/wiki/Hilbert%E2%80%93P%C3%B3lya_conjecture)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- H. L. Montgomery, *The pair correlation of zeros of the zeta function*, Analytic number theory,
  Proc. Sympos. Pure Math. XXIV, AMS (1973), 181–193.
-/

open Complex

namespace HilbertPolyaConjecture

/-- The **Hilbert–Pólya conjecture**: the nontrivial zeros of the Riemann zeta function
correspond to eigenvalues of a self-adjoint operator.

Precisely: there exist a complex Hilbert space $H$ and a (possibly unbounded) self-adjoint
operator $A$ on $H$ such that a complex number $\rho$ is a nontrivial zero of $\zeta$ if and only
if $\rho = \tfrac12 + i\mu$ for some eigenvalue $\mu$ of $A$. Here a nontrivial zero is a
zero $\rho$ of $\zeta$ that is neither a trivial zero $-2(n+1)$, $n \in \mathbb{N}$, nor the
pole $1$, as in Mathlib's `RiemannHypothesis`.

Here `A : H →ₗ.[ℂ] H` is a partially defined linear map, `IsSelfAdjoint A` means `A† = A`,
and $\mu$ is an eigenvalue of `A` if `A x = μ • x` for some nonzero `x` in the domain of
`A`. -/
@[category research open, AMS 11 47]
theorem hilbert_polya_conjecture :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (A : H →ₗ.[ℂ] H), IsSelfAdjoint A ∧
      ∀ ρ : ℂ, (riemannZeta ρ = 0 ∧ (¬ ∃ n : ℕ, ρ = -2 * (n + 1)) ∧ ρ ≠ 1) ↔
        ∃ μ : ℂ, ρ = 1 / 2 + I * μ ∧ ∃ x : A.domain, x ≠ 0 ∧ A x = μ • (x : H) := by
  sorry

/-- The Hilbert–Pólya conjecture implies the Riemann Hypothesis, because the eigenvalues of a
self-adjoint operator are real. -/
@[category test, AMS 11 47]
theorem hilbert_polya_conjecture_implies_riemannHypothesis :
    type_of% hilbert_polya_conjecture → RiemannHypothesis := by
  rintro ⟨H, _, _, _, A, hA, hspec⟩ s hs hs' hs1
  obtain ⟨μ, rfl, x, hx0, hx⟩ := (hspec s).1 ⟨hs, hs', hs1⟩
  have hfa := LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def] at hA
  rw [hA] at hfa
  have h1 := hfa x x
  rw [hx, inner_smul_left, inner_smul_right] at h1
  have hxx : inner ℂ (x : H) (x : H) ≠ 0 := by
    rw [inner_self_ne_zero]
    exact fun h => hx0 (Subtype.ext h)
  have hconj : (starRingEnd ℂ) μ = μ := mul_right_cancel₀ hxx h1
  rw [conj_eq_iff_im] at hconj
  simp [hconj]

end HilbertPolyaConjecture
