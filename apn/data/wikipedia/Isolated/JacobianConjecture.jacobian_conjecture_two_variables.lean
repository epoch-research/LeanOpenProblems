/-
Copyright 2025 The Formal Conjectures Authors.

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
# Jacobian conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Jacobian_conjecture)
-/

namespace JacobianConjecture

section Conjecture

open MvPolynomial RegularFunction

variable (k : Type*)

name_poly_vars X, Y, Z over k

/-- Alpöge/Fable's counterexample: a polynomial self-map of `k³` with Jacobian
determinant `-2` which is not injective. -/
noncomputable abbrev F [CommRing k] : RegularFunction k (Fin 3) (Fin 3) :=
  ![(1 + X * Y)^3 * Z + Y ^ 2 * (1 + X * Y) * (4 + 3 * X * Y),
    Y + 3 * X * (1 + X * Y) ^ 2 * Z + 3 * X * Y ^ 2 * (4 + 3 * X * Y),
    2 * X - 3 * X ^ 2 * Y - X ^ 3 * Z]

/-- A variant of Alpöge/Fable's counterexample: a polynomial self-map of `k³` with Jacobian
determinant `1` which is not injective. -/
noncomputable abbrev G [CommRing k] : RegularFunction k (Fin 3) (Fin 3) :=
  ![(1 + 2 * X * Y) ^ 3 * Z + 4 * Y ^ 2 * (1 + 2 * X * Y) * (2 + 3 * (X * Y)),
    Y + 3 * X * (1 + 2 * X * Y) ^ 2 * Z + 12 * X * Y ^ 2 * (2 + 3 * (X * Y)),
    -X + 3 * X ^ 2 * Y + X ^ 3 * Z]

/-- The predicate that the Jacobian conjecture holds for a given field and variable index type
(i.e. number of variables). -/
def JacobianConjectureProp (k σ : Type*) [CommRing k] [Fintype σ] [DecidableEq σ] : Prop :=
  ∀ (F : RegularFunction k σ σ), IsUnit F.Jacobian.det →
    ∃ (G : RegularFunction k σ σ), G.comp F = id k σ ∧
    F.comp G = id k σ

/-- Does the Jacobian conjecture hold in the two variable case? -/
theorem jacobian_conjecture_two_variables :
    ∀ {k : Type} [Field k] [CharZero k], JacobianConjectureProp k (Fin 2) := by
  sorry

end Conjecture

section Tests

open MvPolynomial RegularFunction

variable {k σ : Type} [Fintype σ] [DecidableEq σ] [Field k]

end Tests

end JacobianConjecture

theorem JacobianConjecture.jacobian_conjecture_two_variables.disproof : ¬ (type_of% @JacobianConjecture.jacobian_conjecture_two_variables) := sorry
