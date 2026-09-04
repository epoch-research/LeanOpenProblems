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
# Skolem problem

The Skolem problem (also called the Skolem–Pisot problem) asks whether there is an algorithm
that, given a constant-recursive sequence, decides whether the sequence contains the number zero.

A constant-recursive sequence is specified by finitely many data: the order $d$ and the
coefficients $a_0, \dots, a_{d-1}$ of a linear recurrence relation
$$u_{n + d} = a_0 u_n + a_1 u_{n + 1} + \dots + a_{d-1} u_{n + d - 1} \qquad (n \ge 0),$$
together with the initial values $u_0, \dots, u_{d-1}$. These data determine the sequence
$(u_n)_{n \ge 0}$ uniquely.

The problem can be posed for recurrences over the integers, the rational numbers or the
algebraic numbers. We state the integer version. The rational version reduces to it by
clearing denominators: if $D$ is a common denominator of the coefficients, then
$v_n = D^n u_n$ satisfies an integer recurrence and has the same zeros as $u$.

*References:*
- [Wikipedia, Skolem problem](https://en.wikipedia.org/wiki/Skolem_problem)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Tao, Open question: effective Skolem–Mahler–Lech theorem](https://terrytao.wordpress.com/2007/05/25/open-question-effective-skolem-mahler-lech-theorem/)
-/

namespace SkolemProblem

/--
The data specifying an integer constant-recursive sequence: a linear recurrence relation
`u (n + d) = ∑ i : Fin d, coeffs i * u (n + i)` with integer coefficients (as a Mathlib
`LinearRecurrence ℤ`) together with the `d` initial values `u 0, …, u (d - 1)`, where `d` is
the order of the recurrence.
-/
structure RecurrenceWithInit where
  /-- The linear recurrence relation with constant integer coefficients. -/
  recurrence : LinearRecurrence ℤ
  /-- The initial values of the sequence. -/
  init : Fin recurrence.order → ℤ

/--
A `RecurrenceWithInit` of order `d` is the same data as a list of `d` pairs
`(coefficient, initial value)`. This is used to encode it as a `Primcodable` type.
-/
def RecurrenceWithInit.equivList : RecurrenceWithInit ≃ List (ℤ × ℤ) :=
  Equiv.trans
    { toFun := fun r => ⟨r.recurrence.order, fun i => (r.recurrence.coeffs i, r.init i)⟩
      invFun := fun p => ⟨⟨p.1, fun i => (p.2 i).1⟩, fun i => (p.2 i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    List.equivSigmaTuple.symm

/-- A `RecurrenceWithInit` is a finite object, so it can be given as input to an algorithm. -/
instance : Primcodable RecurrenceWithInit :=
  .ofEquiv _ RecurrenceWithInit.equivList

/--
The constant-recursive sequence `u : ℕ → ℤ` determined by a recurrence relation and initial
values: `u n = init n` for `n < d`, and `u (n + d) = ∑ i : Fin d, coeffs i * u (n + i)` for
all `n`.
-/
def RecurrenceWithInit.seq (r : RecurrenceWithInit) : ℕ → ℤ :=
  r.recurrence.mkSol r.init

/--
**Skolem problem.** Is there an algorithm which, given a constant-recursive sequence of integers
(specified by an integer linear recurrence relation together with its initial values), decides
whether the sequence contains a zero, i.e. whether $u_n = 0$ for some $n \ge 0$?

Formally: is the predicate `∃ n, r.seq n = 0` on the `Primcodable` type `RecurrenceWithInit` a
computable predicate?
-/
theorem skolem_problem :
    ComputablePred fun r : RecurrenceWithInit => ∃ n, r.seq n = 0 := by
  sorry

/-- The Fibonacci numbers, given by `F (n + 2) = F n + F (n + 1)`, `F 0 = 0` and `F 1 = 1`. -/
def fibonacci : RecurrenceWithInit := ⟨⟨2, ![1, 1]⟩, ![0, 1]⟩

/-- The constant sequence `1, 1, 1, …`, given by `u (n + 1) = u n` with `u 0 = 1`. -/
def constOne : RecurrenceWithInit := ⟨⟨1, ![1]⟩, ![1]⟩

end SkolemProblem

theorem SkolemProblem.skolem_problem.disproof : ¬ (type_of% @SkolemProblem.skolem_problem) := sorry
