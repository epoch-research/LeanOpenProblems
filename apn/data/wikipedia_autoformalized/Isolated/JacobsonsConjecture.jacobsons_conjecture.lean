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
# Jacobson's conjecture

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Jacobson%27s_conjecture)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
-/

namespace JacobsonsConjecture

/--
**Jacobson's conjecture**: the intersection of all powers of the Jacobson radical of a
left-and-right Noetherian ring is precisely $0$. That is, if $R$ is a ring that is both left
and right Noetherian and $J$ is its Jacobson radical, then
$$\bigcap_{n \in \mathbb{N}} J^n = \{0\},$$
where the powers $J^n$ are products of ideals.

Here `Ring.jacobson R` is the Jacobson radical $J$ of `R` (a two-sided ideal, so its powers
`Ring.jacobson R ^ n` are the usual products of ideals). Mathlib's `IsNoetherianRing R` says that
`R` is left Noetherian, so `IsNoetherianRing Rᵐᵒᵖ` says that `R` is right Noetherian. The
two-sided Noetherian hypothesis is essential: the conjecture is false for one-sided Noetherian
rings (Herstein 1965, Jategaonkar 1968). The term `n = 0` gives `Ring.jacobson R ^ 0 = ⊤`, which
does not affect the intersection.
-/
theorem jacobsons_conjecture (R : Type*) [Ring R] [IsNoetherianRing R]
    [IsNoetherianRing Rᵐᵒᵖ] : ⨅ n : ℕ, Ring.jacobson R ^ n = ⊥ := by
  sorry

end JacobsonsConjecture

theorem JacobsonsConjecture.jacobsons_conjecture.disproof : ¬ (type_of% @JacobsonsConjecture.jacobsons_conjecture) := sorry
