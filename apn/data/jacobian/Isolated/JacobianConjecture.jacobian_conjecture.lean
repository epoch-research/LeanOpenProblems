import FormalConjecturesUtil

/-!
# Jacobian conjecture

Let `n ≥ 1`. A polynomial map `F : ℂⁿ → ℂⁿ` is a map `F(x) = (F₁(x), ..., Fₙ(x))` where each
`Fᵢ ∈ ℂ[x₁, ..., xₙ]`. Its Jacobian determinant is `det J_F = det (∂Fᵢ/∂xⱼ)`. The Jacobian
conjecture asserts that every polynomial map `F : ℂⁿ → ℂⁿ` with nonzero constant Jacobian
determinant has a polynomial inverse.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Jacobian_conjecture)
-/

namespace JacobianConjecture

open MvPolynomial RegularFunction

/-- The predicate that the Jacobian conjecture holds for a given field and variable index type
(i.e. number of variables). -/
def JacobianConjectureProp (k σ : Type*) [CommRing k] [Fintype σ] [DecidableEq σ] : Prop :=
  ∀ (F : RegularFunction k σ σ), IsUnit F.Jacobian.det →
    ∃ (G : RegularFunction k σ σ), G.comp F = id k σ ∧
    F.comp G = id k σ

/-- The **Jacobian Conjecture** over `ℂ`: for every `n`, every polynomial map `ℂⁿ → ℂⁿ` whose
Jacobian determinant is a nonzero constant has a polynomial inverse. -/
theorem jacobian_conjecture : ∀ n : ℕ, JacobianConjectureProp ℂ (Fin n) := by
  sorry

end JacobianConjecture

theorem JacobianConjecture.jacobian_conjecture.disproof : ¬ (type_of% @JacobianConjecture.jacobian_conjecture) := sorry
