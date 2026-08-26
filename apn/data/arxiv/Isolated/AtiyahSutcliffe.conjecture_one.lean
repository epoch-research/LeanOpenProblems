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
# The first Atiyah--Sutcliffe conjecture

Atiyah and Sutcliffe associate a homogeneous binary polynomial to each point
in a configuration of distinct points in Euclidean three-space. Their first
conjecture says that these polynomials are always linearly independent.

*References:*
- M. F. Atiyah and P. M. Sutcliffe,
  [The Geometry of Point Particles](https://doi.org/10.1098/rspa.2001.0913)
- Marcin Mazur and Bogdan V. Petrenko,
  [On the conjectures of Atiyah and Sutcliffe](https://arxiv.org/abs/1102.4662)
-/

namespace AtiyahSutcliffe

noncomputable section

open MvPolynomial

/-- A point of Euclidean three-space. -/
abbrev Point := EuclideanSpace ℝ (Fin 3)

/-- A deterministic projective lift of a direction in $\mathbb{R}^3$ to a pair of complex
numbers.

Away from the north pole this is the representative $(z / w, 1)$ from stereographic
projection. At the north pole the denominator vanishes, so we use $(1, 0)$.

This is an unnormalized lift that does not impose the antisymmetric $\mathrm{SU}(2)$ convention
of Atiyah–Sutcliffe. Since linear independence is invariant under rescaling each polynomial by
a nonzero constant, this suffices for Conjecture 1. It would not suffice for Conjectures 2 or 3,
which depend on the normalization $|z|^2 + |w|^2 = 1$. -/
def directionLift (v : Point) : ℂ × ℂ :=
  if ‖v‖ - v 2 = 0 then
    (1, 0)
  else
    (((v 0 : ℂ) + (v 1 : ℂ) * Complex.I) / (‖v‖ - v 2 : ℝ), 1)

/-- The homogeneous linear factor determined by a lifted direction. -/
def linearFactor (zw : ℂ × ℂ) : MvPolynomial (Fin 2) ℂ :=
  C zw.1 * X 0 - C zw.2 * X 1

/-- The polynomial associated to point `i` in a finite configuration `x`. -/
def pointPolynomial {n : ℕ} (x : Fin n → Point) (i : Fin n) :
    MvPolynomial (Fin 2) ℂ :=
  ∏ j ∈ Finset.univ.erase i, linearFactor (directionLift (x j - x i))

/-- [Atiyah–Sutcliffe Conjecture 1](https://doi.org/10.1098/rspa.2001.0913), stated as
Conjecture 1.1 in [Mazur–Petrenko](https://arxiv.org/abs/1102.4662): the configuration
polynomials are linearly independent. -/
theorem conjecture_one {n : ℕ} (x : Fin n → Point) (hx : Function.Injective x) :
    LinearIndependent ℂ (pointPolynomial x) := by
  sorry

end

end AtiyahSutcliffe
