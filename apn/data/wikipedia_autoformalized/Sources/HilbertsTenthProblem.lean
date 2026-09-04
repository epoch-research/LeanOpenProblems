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
# Hilbert's tenth problem for number fields

Hilbert's tenth problem asks for an algorithm which decides, for any given polynomial equation
with integer coefficients in any number of unknowns, whether it has a solution in the integers.
By the MRDP theorem (Davis, Putnam, Robinson, Matiyasevich, 1970) no such algorithm exists.

The same question can be asked for any countable ring $R$: *Hilbert's tenth problem for $R$*
asks for an algorithm which decides, for any polynomial equation with coefficients in $R$,
whether it has a solution in $R$. Wikipedia's list of unsolved problems asks: *for which number
fields does Hilbert's tenth problem hold?* Following the Wikipedia article, this is read as the
question for the rings of integers $\mathcal{O}_K$ of number fields $K$. Undecidability was known
for many classes of number fields (Denef–Lipshitz, Shapiro–Shlapentokh, Pheidas, Videla, ...).
Koymans–Pagano (2024) and Alpöge–Bhargava–Ho–Shnidman (2025) have announced proofs that
Hilbert's tenth problem is undecidable for the ring of integers of *every* number field.
The problem for equations over the field $\mathbb{Q}$ itself remains open.

To speak about algorithms, a polynomial equation `P = 0` over a ring `R` is given by a *code*:
a finite list of terms `(c, m)`, where `c` codes a coefficient of `R` (decoded by a fixed map
`f`) and `m : List (ℕ × ℕ)` lists pairs `(i, k)` standing for the factors `X i ^ k` of a
monomial in the unknowns `X 0, X 1, …`. Every polynomial over `R` has such a code
(`PolyCode.toMvPolynomial_surjective`). The existence of an algorithm is rendered by
`ComputablePred` on the codes. For `R = 𝓞 K` the coefficients are coded by their coordinates
with respect to a `ℤ`-basis of `𝓞 K`; for `R = ℚ` they are rational numbers.

*References:*
- [Wikipedia, *Hilbert's tenth problem*](https://en.wikipedia.org/wiki/Hilbert%27s_tenth_problem)
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [P. Koymans, C. Pagano, *Hilbert's tenth problem via additive combinatorics*](https://arxiv.org/abs/2412.01768)
- [L. Alpöge, M. Bhargava, W. Ho, A. Shnidman, *Rank stability in quadratic extensions and
  Hilbert's tenth problem for the ring of integers of a number field*](https://arxiv.org/abs/2501.18774)
-/

namespace HilbertsTenthProblem

open MvPolynomial NumberField

variable {α R : Type*} [CommSemiring R]

/--
A code for a polynomial equation `P = 0` in the unknowns `X 0, X 1, …`, with coefficients coded
by elements of `α`. A code is a finite list of terms `(c, m)`: `c : α` codes the coefficient of
the term and `m` lists pairs `(i, k)` standing for the factors `X i ^ k` of its monomial.
-/
abbrev PolyCode (α : Type*) := List (α × List (ℕ × ℕ))

/--
The polynomial `∑ (c, m) ∈ p, f c * ∏ (i, k) ∈ m, X i ^ k` coded by `p`, where `f` decodes
the coefficients.
-/
noncomputable def PolyCode.toMvPolynomial (f : α → R) (p : PolyCode α) : MvPolynomial ℕ R :=
  (p.map fun t => C (f t.1) * (t.2.map fun ik => X ik.1 ^ ik.2).prod).sum

/--
The polynomial equation coded by `p` (with coefficients decoded by `f : α → R`) has a solution
in `R`. Only the finitely many unknowns occurring in `p` matter.
-/
def PolyCode.HasSolution (f : α → R) (p : PolyCode α) : Prop :=
  ∃ x : ℕ → R, eval x (p.toMvPolynomial f) = 0

/-- Every polynomial over `R` is coded by some `p : PolyCode α` when `f : α → R` is surjective. -/
@[category API, AMS 3 12]
theorem PolyCode.toMvPolynomial_surjective {f : α → R} (hf : Function.Surjective f) :
    Function.Surjective (PolyCode.toMvPolynomial f) := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨c, rfl⟩ := hf a
    exact ⟨[(c, [])], by simp [PolyCode.toMvPolynomial]⟩
  | add P Q hP hQ =>
    obtain ⟨p, rfl⟩ := hP
    obtain ⟨q, rfl⟩ := hQ
    exact ⟨p ++ q, by simp [PolyCode.toMvPolynomial]⟩
  | mul_X P i hP =>
    obtain ⟨p, rfl⟩ := hP
    refine ⟨p.map fun t => (t.1, t.2 ++ [(i, 1)]), ?_⟩
    simp only [PolyCode.toMvPolynomial, List.map_map, Function.comp_def, List.map_append,
      List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, pow_one,
      mul_one, ← mul_assoc]
    rw [List.sum_map_mul_right]

/-- The code of the equation $x^2 + y^2 + 1 = 0$ over `ℤ`. -/
@[category test, AMS 3 11]
theorem PolyCode.toMvPolynomial_example :
    PolyCode.toMvPolynomial (id : ℤ → ℤ) [(1, [(0, 2)]), (1, [(1, 2)]), (1, [])] =
      X 0 ^ 2 + X 1 ^ 2 + 1 := by
  simp [PolyCode.toMvPolynomial, add_assoc]

/-- The equation $x^2 + y^2 + 1 = 0$ has no integer solution. -/
@[category test, AMS 3 11]
theorem PolyCode.not_hasSolution_example :
    ¬ PolyCode.HasSolution (id : ℤ → ℤ) [(1, [(0, 2)]), (1, [(1, 2)]), (1, [])] := by
  rintro ⟨x, hx⟩
  simp [PolyCode.toMvPolynomial] at hx
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

/-- The equation $3x^2 - 2xy - y^2z - 7 = 0$ has the integer solution $x = 1$, $y = 2$,
$z = -2$. -/
@[category test, AMS 3 11]
theorem PolyCode.hasSolution_example :
    PolyCode.HasSolution (id : ℤ → ℤ)
      [(3, [(0, 2)]), (-2, [(0, 1), (1, 1)]), (-1, [(1, 2), (2, 1)]), (-7, [])] := by
  refine ⟨fun n => match n with | 0 => 1 | 1 => 2 | _ => -2, ?_⟩
  simp [PolyCode.toMvPolynomial]

/--
The ring of integers of a number field has a `ℤ`-basis indexed by `Fin d` for some `d`, so the
hypothesis of `hilberts_tenth_problem` can be satisfied for every number field.
-/
@[category API, AMS 11]
theorem exists_basis (K : Type*) [Field K] [NumberField K] :
    ∃ d : ℕ, Nonempty (Module.Basis (Fin d) ℤ (𝓞 K)) :=
  ⟨_, ⟨Module.finBasis ℤ (𝓞 K)⟩⟩

/--
**Hilbert's tenth problem for the ring of integers of a number field.**

Wikipedia's list of unsolved problems asks: *for which number fields does Hilbert's tenth
problem hold?* Read as the classical question for rings of integers, the expected answer is
"for every number field": for every number field $K$ there is no algorithm which decides, for
any given polynomial equation with coefficients in $\mathcal{O}_K$ in any number of unknowns,
whether it has a solution in $\mathcal{O}_K$.

Elements of `𝓞 K` are coded by their coordinate vectors `Fin d → ℤ` with respect to a `ℤ`-basis
`b` of `𝓞 K` (decoded by `b.equivFun.symm`), and polynomial equations by `PolyCode (Fin d → ℤ)`.
Any two such bases differ by an integer matrix, so decidability does not depend on `b`.

Proofs of this statement have been announced by Koymans–Pagano (2024) and by
Alpöge–Bhargava–Ho–Shnidman (2025).
-/
@[category research open, AMS 3 11]
theorem hilberts_tenth_problem (K : Type*) [Field K] [NumberField K] {d : ℕ}
    (b : Module.Basis (Fin d) ℤ (𝓞 K)) :
    ¬ ComputablePred fun p : PolyCode (Fin d → ℤ) => p.HasSolution b.equivFun.symm := by
  sorry

/--
**Hilbert's tenth problem over the rationals.**

Does there exist an algorithm which decides, for any given polynomial equation with rational
coefficients in any number of unknowns, whether it has a solution in rational numbers?
Here `answer(True)` means that such an algorithm exists. Despite much interest, this problem
remains open.
-/
@[category research open, AMS 3 11]
theorem hilberts_tenth_problem.variants.rationals :
    answer(sorry) ↔ ComputablePred fun p : PolyCode ℚ => p.HasSolution id := by
  sorry

end HilbertsTenthProblem
