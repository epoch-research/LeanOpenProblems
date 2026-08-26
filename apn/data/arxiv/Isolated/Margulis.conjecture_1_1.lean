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
# A conjecture by Margulis on matrix groups

*Reference:* [arxiv/2504.17644v3](https://arxiv.org/abs/2504.17644v3)
**Bounded diagonal orbits in homogeneous spaces over function fields**
by *Qianlin Huang, Ronggang Shi*
-/

namespace Margulis

open Matrix SpecialLinearGroup
open scoped MatrixGroups Polynomial LaurentSeries

section

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

/-- Let `D` be the diagonal group of `SL_n(ℝ)` where n ≥ 3.
Then any relatively compact `D`-orbit in `SL_n(ℝ) / SL_n(ℤ)` is closed. -/
theorem conjecture_1_1 {n : ℕ} (hn : 3 ≤ n)
    (g : SL(n, ℝ) ⧸ Subgroup.map (map (Int.castRingHom ℝ)) ⊤)
    (hg : IsCompact <| closure (MulAction.orbit (diagonalSubgroup (Fin n) ℝ) g)) :
    IsClosed <| MulAction.orbit (diagonalSubgroup (Fin n) ℝ) g := by
  sorry

end

 /-
## Diagonal orbits over function fields (Huang–Shi, Theorem 1.2)

We now formulate a Lean version of the main theorem of Huang–Shi.
Let `F` be a finite field of characteristic `p ∈ {3, 5, 7, 11}`. Set

* `A = F[t]`,
* `K = F((t⁻¹))`.

Denote by `D` the diagonal subgroup of `SL₄(K)` and by `Γ` the lattice
subgroup `SL₄(A)` embedded into `SL₄(K)` via the natural map `A →+* K`.

Then there exists a point `z : SL₄(K)/Γ` such that the `D`-orbit of `z` has
compact closure but is not closed.
-/

universe u

section FunctionFieldDiagonalOrbit

variable (F : Type u) [Field F] [Fintype F]

/-- The natural inclusion `F[t] →+* F((t⁻¹))`. -/
noncomputable def polyToLaurent : F[X] →+* F⸨X⸩ :=
  (HahnSeries.ofPowerSeries ℤ F).comp Polynomial.coeToPowerSeries.ringHom

end FunctionFieldDiagonalOrbit

end Margulis
