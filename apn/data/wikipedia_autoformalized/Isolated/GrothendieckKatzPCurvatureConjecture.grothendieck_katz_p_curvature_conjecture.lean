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
# Grothendieck–Katz $p$-curvature conjecture

A conjectured local–global principle for linear ordinary differential equations: a linear
differential system $dY/dz = A(z)\,Y$ with $A \in M_n(\mathbb{Q}(z))$ has a full set of algebraic
solutions as soon as, for all but finitely many primes $p$, its reduction modulo $p$ has
$p$-curvature zero (equivalently, has a full set of solutions in $\mathbb{F}_p(z)$).

The $p$-curvature is computed by the recurrence $A_0 = I$, $A_{k+1} = A_k' + A_k A$ (so that
$d^kY/dz^k = A_k Y$ for every solution $Y$): the $p$-curvature of the reduction modulo $p$ vanishes
if and only if $A_p \equiv 0 \pmod p$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Grothendieck%E2%80%93Katz_p-curvature_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- A. Chambert-Loir, *Théorèmes d'algébrisation en géométrie diophantienne*, Séminaire Bourbaki
  Exp. 886, §3, [arXiv:math/0103192](https://arxiv.org/abs/math/0103192)
- N. M. Katz, *Algebraic solutions of differential equations ($p$-curvature and the Hodge
  filtration)*, Invent. Math. 18 (1972), 1–118
- N. M. Katz, *A conjecture in the arithmetic theory of differential equations*, Bull. Soc. Math.
  France 110 (1982), 203–239
- L. Di Vizio, *Arithmetic theory of $q$-difference equations*, Invent. Math. 150 (2002),
  [arXiv:math/0104178](https://arxiv.org/abs/math/0104178)
-/

namespace GrothendieckKatzPCurvatureConjecture

open Polynomial RatFunc
open scoped Differential

/- ### The differential field `K(X)`

Mathlib has no derivation on `RatFunc K`. We define `d/dX` by the quotient rule on the reduced
numerator and denominator and record it as a `Differential` instance, so that the unique extension
of `d/dX` to finite extensions of `K(X)` (`Differential.differentialFiniteDimensional`) is
available. -/

section RatFuncDerivative

variable {K : Type*} [Field K]

/-- The derivative `d/dX` of a rational function `r = f / g` (with `f = r.num`, `g = r.denom`),
given by the quotient rule `(f' g - f g') / g ^ 2`. -/
noncomputable def ratFuncDerivative (r : RatFunc K) : RatFunc K :=
  (algebraMap K[X] (RatFunc K) (derivative r.num) * algebraMap K[X] (RatFunc K) r.denom -
      algebraMap K[X] (RatFunc K) r.num * algebraMap K[X] (RatFunc K) (derivative r.denom)) /
    algebraMap K[X] (RatFunc K) r.denom ^ 2

/-- The quotient rule holds for any representation `p / q` of a rational function, not only for
the reduced one. -/
theorem ratFuncDerivative_div (p q : K[X]) (hq : q ≠ 0) :
    ratFuncDerivative (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
      (algebraMap K[X] (RatFunc K) (derivative p) * algebraMap K[X] (RatFunc K) q -
          algebraMap K[X] (RatFunc K) p * algebraMap K[X] (RatFunc K) (derivative q)) /
        algebraMap K[X] (RatFunc K) q ^ 2 := by
  set r := algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q with hr
  have h1 : r.num * q = p * r.denom := (num_mul_eq_mul_denom_iff hq).mpr hr
  have h2 : derivative r.num * q + r.num * derivative q =
      derivative p * r.denom + p * derivative r.denom := by
    simpa only [derivative_mul] using congrArg derivative h1
  have key : (derivative r.num * r.denom - r.num * derivative r.denom) * q ^ 2 =
      (derivative p * q - p * derivative q) * r.denom ^ 2 := by
    linear_combination (r.denom * q) * h2 - (derivative q * r.denom + derivative r.denom * q) * h1
  unfold ratFuncDerivative
  rw [div_eq_div_iff (pow_ne_zero 2 (algebraMap_ne_zero (denom_ne_zero r)))
    (pow_ne_zero 2 (algebraMap_ne_zero hq))]
  simpa only [map_mul, map_sub, map_pow] using congrArg (algebraMap K[X] (RatFunc K)) key

theorem ratFuncDerivative_add (x y : RatFunc K) :
    ratFuncDerivative (x + y) = ratFuncDerivative x + ratFuncDerivative y := by
  induction x using RatFunc.induction_on with | _ p₁ q₁ hq₁ => ?_
  induction y using RatFunc.induction_on with | _ p₂ q₂ hq₂ => ?_
  rw [div_add_div _ _ (algebraMap_ne_zero hq₁) (algebraMap_ne_zero hq₂), ← map_mul,
    ← map_mul, ← map_add, ← map_mul, ratFuncDerivative_div _ _ (mul_ne_zero hq₁ hq₂),
    ratFuncDerivative_div _ _ hq₁, ratFuncDerivative_div _ _ hq₂]
  have h₁ := algebraMap_ne_zero (K := K) hq₁
  have h₂ := algebraMap_ne_zero (K := K) hq₂
  simp only [derivative_mul, map_add, map_mul]
  field_simp
  ring

theorem ratFuncDerivative_mul (x y : RatFunc K) :
    ratFuncDerivative (x * y) = x * ratFuncDerivative y + y * ratFuncDerivative x := by
  induction x using RatFunc.induction_on with | _ p₁ q₁ hq₁ => ?_
  induction y using RatFunc.induction_on with | _ p₂ q₂ hq₂ => ?_
  rw [div_mul_div_comm, ← map_mul, ← map_mul,
    ratFuncDerivative_div _ _ (mul_ne_zero hq₁ hq₂), ratFuncDerivative_div _ _ hq₁,
    ratFuncDerivative_div _ _ hq₂]
  have h₁ := algebraMap_ne_zero (K := K) hq₁
  have h₂ := algebraMap_ne_zero (K := K) hq₂
  simp only [derivative_mul, map_add, map_mul]
  field_simp
  ring

/-- `ratFuncDerivative` as an additive map. -/
noncomputable def ratFuncDerivativeAddHom : RatFunc K →+ RatFunc K :=
  AddMonoidHom.mk' ratFuncDerivative ratFuncDerivative_add

/-- The field `K(X)` of rational functions is a differential field for the derivation `d/dX`. -/
noncomputable instance : Differential (RatFunc K) where
  deriv := @Derivation.mk' ℤ _ (RatFunc K) _ (Ring.toIntAlgebra _) (RatFunc K) _ _ _
    (ratFuncDerivativeAddHom (K := K)).toIntLinearMap ratFuncDerivative_mul

end RatFuncDerivative

/- ### The matrices `A_k` and the `p`-curvature -/

section HigherDerivMatrix

variable {R : Type*} [CommRing R] [Differential R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For a matrix `A` over a differential ring, `higherDerivMatrix A k` is the matrix `A_k` defined
by the recurrence `A_0 = 1`, `A_{k+1} = A_k' + A_k A` (where `A_k'` is the entrywise derivative),
so that every solution `Y` of `Y' = A Y` satisfies `Y^{(k)} = A_k Y`.

For `A` over `ℚ(z)` and a prime `p`, the reduction modulo `p` of `A_p` is the `p`-curvature of
the reduction modulo `p` of the system `Y' = A Y`. -/
noncomputable def higherDerivMatrix (A : Matrix ι ι R) : ℕ → Matrix ι ι R
  | 0 => 1
  | k + 1 => (higherDerivMatrix A k).map (·′) + higherDerivMatrix A k * A

end HigherDerivMatrix

/- ### Reduction modulo `p` of rational functions over `ℚ` -/

section ReductionModP

/-- A rational function `r ∈ ℚ(z)` is *`p`-integral* (its reduction modulo `p` is defined) if
`r = f / g` with `f, g ∈ ℤ[z]` and `g ≢ 0 (mod p)`. Equivalently, `r` has `p`-adic Gauss norm
at most `1`. -/
def IsPIntegral (p : ℕ) (r : RatFunc ℚ) : Prop :=
  ∃ f g : ℤ[X], g.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
    r = algebraMap ℚ[X] (RatFunc ℚ) (f.map (Int.castRingHom ℚ)) /
      algebraMap ℚ[X] (RatFunc ℚ) (g.map (Int.castRingHom ℚ))

/-- A rational function `r ∈ ℚ(z)` is *zero modulo `p`* if `r = f / g` with `f, g ∈ ℤ[z]`,
`g ≢ 0 (mod p)` and `f ≡ 0 (mod p)`. Equivalently, `r` has `p`-adic Gauss norm less than `1`,
i.e. `r` is `p`-integral and its reduction in `𝔽_p(z)` is `0`. -/
def IsZeroModP (p : ℕ) (r : RatFunc ℚ) : Prop :=
  ∃ f g : ℤ[X], g.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
    f.map (Int.castRingHom (ZMod p)) = 0 ∧
    r = algebraMap ℚ[X] (RatFunc ℚ) (f.map (Int.castRingHom ℚ)) /
      algebraMap ℚ[X] (RatFunc ℚ) (g.map (Int.castRingHom ℚ))

/-- The linear differential system `Y' = A Y`, for `A` an `n × n` matrix over `ℚ(z)`, has
*`p`-curvature zero modulo `p`*: `A` can be reduced modulo `p` (all its entries are `p`-integral)
and the `p`-curvature matrix `A_p` of the reduction is zero, i.e. `A_p ≡ 0 (mod p)` entrywise.
By a theorem of Cartier, this holds if and only if the reduction modulo `p` of the system has a
full set of solutions in `𝔽_p(z)` (equivalently, of solutions algebraic over `𝔽_p(z)`). -/
def HasPCurvatureZero {n : ℕ} (p : ℕ) (A : Matrix (Fin n) (Fin n) (RatFunc ℚ)) : Prop :=
  (∀ i j, IsPIntegral p (A i j)) ∧ ∀ i j, IsZeroModP p (higherDerivMatrix A p i j)

end ReductionModP

/- ### Full sets of algebraic solutions -/

section AlgebraicSolutions

variable {F : Type*} [Field F] [Differential F] [CharZero F]

/-- The linear differential system `Y' = A Y`, for `A` an `n × n` matrix over a differential
field `F` of characteristic `0`, has a *full set of algebraic solutions*: there is a fundamental
matrix of solutions, i.e. an invertible `n × n` matrix `Y` with `Y' = A Y`, whose entries lie in
a finite extension `L` of `F` (inside an algebraic closure of `F`). Here `L` carries the unique
derivation extending that of `F`. -/
def HasFullSetOfAlgebraicSolutions {n : ℕ} (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∃ (L : IntermediateField F (AlgebraicClosure F)) (_ : FiniteDimensional F L)
    (Y : Matrix (Fin n) (Fin n) L),
    IsUnit Y ∧ Y.map (·′) = A.map (algebraMap F L) * Y

end AlgebraicSolutions

/-- **Grothendieck–Katz $p$-curvature conjecture** (Grothendieck's conjecture, in its essential
case). Let $A$ be an $n \times n$ matrix of rational functions in $\mathbb{Q}(z)$, and consider
the linear differential system $dY/dz = A(z)\,Y$. Let $A_0 = I$ and $A_{k+1} = A_k' + A_k A$, so
that $d^kY/dz^k = A_k Y$ for every solution $Y$.

Suppose that for all but finitely many primes $p$, the system can be reduced modulo $p$ and the
reduced system has $p$-curvature zero, i.e. $A_p \equiv 0 \pmod p$ (equivalently, the reduced
system has a full set of solutions in $\mathbb{F}_p(z)$, or algebraic over $\mathbb{F}_p(z)$).
Then the system has a full set of algebraic solutions: a fundamental matrix
$Y \in \mathrm{GL}_n(L)$ with $Y' = AY$, whose entries lie in a finite extension $L$ of
$\mathbb{Q}(z)$.

Only this sufficiency direction is conjectural; the converse (necessity of the mod $p$ condition)
is a classical theorem of Cartier and Katz. -/
theorem grothendieck_katz_p_curvature_conjecture {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (RatFunc ℚ))
    (hA : ∀ᶠ p in Filter.cofinite, p.Prime → HasPCurvatureZero p A) :
    HasFullSetOfAlgebraicSolutions A := by
  sorry

end GrothendieckKatzPCurvatureConjecture

theorem GrothendieckKatzPCurvatureConjecture.grothendieck_katz_p_curvature_conjecture.disproof : ¬ (type_of% @GrothendieckKatzPCurvatureConjecture.grothendieck_katz_p_curvature_conjecture) := sorry
