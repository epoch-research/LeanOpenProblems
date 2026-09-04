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
# Tarski's exponential function problem

Tarski proved that the first-order theory of the ordered field of real numbers
$(\mathbb{R}, +, \cdot, -, <, 0, 1)$ is decidable: there is an effective procedure
which, given any sentence $\varphi$ in the language of ordered rings, determines whether
$\mathbb{R} \models \varphi$. He then asked whether this remains true when the language is
extended by a unary function symbol $\exp$ interpreted as the real exponential function,
giving the structure $\mathbb{R}_{\exp} = (\mathbb{R}, +, \cdot, -, <, 0, 1, \exp)$.

Macintyre and Wilkie showed that Schanuel's conjecture (in fact, a real version of it) implies
that $\operatorname{Th}(\mathbb{R}_{\exp})$ is decidable, and that decidability of
$\operatorname{Th}(\mathbb{R}_{\exp})$ is equivalent to their "weak Schanuel's conjecture".
Unconditionally, the problem is open.

We formalise decidability of a theory in the classical way: a Gödel numbering assigns to
each sentence a natural number, and the theory is decidable if the set of Gödel numbers of
its sentences is a computable set of natural numbers. The Gödel numbering used here is
Mathlib's `FirstOrder.Language.BoundedFormula.listEncode` (an injective encoding of formulas as
lists of symbols) composed with the standard `Encodable` encoding of lists.

*References:*
- [Wikipedia, Tarski's exponential function problem](https://en.wikipedia.org/wiki/Tarski%27s_exponential_function_problem)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- A. Macintyre, A. J. Wilkie, *On the decidability of the real exponential field*, in:
  Kreiseliana: about and around Georg Kreisel, A K Peters (1996), 441–467.
-/

namespace TarskisExponentialFunctionProblem

open FirstOrder FirstOrder.Language

/-- The function symbols of the language of the real exponential field:
the constants `0`, `1`, the unary operations `-`, `exp` and the binary operations `+`, `*`. -/
inductive ExpFunc : ℕ → Type
  | zero : ExpFunc 0
  | one : ExpFunc 0
  | neg : ExpFunc 1
  | exp : ExpFunc 1
  | add : ExpFunc 2
  | mul : ExpFunc 2
  deriving DecidableEq

/-- The relation symbols of the language of the real exponential field: the binary relation `<`. -/
inductive ExpRel : ℕ → Type
  | lt : ExpRel 2
  deriving DecidableEq

/-- The language of ordered rings `(+, ·, -, <, 0, 1)` extended by a unary function symbol
`exp`. -/
def expLanguage : Language := ⟨ExpFunc, ExpRel⟩

/-- An explicit enumeration of the six function symbols of `expLanguage`. -/
def expFuncEquivFin : (Σ n, expLanguage.Functions n) ≃ Fin 6 where
  toFun
    | ⟨_, .zero⟩ => 0
    | ⟨_, .one⟩ => 1
    | ⟨_, .neg⟩ => 2
    | ⟨_, .exp⟩ => 3
    | ⟨_, .add⟩ => 4
    | ⟨_, .mul⟩ => 5
  invFun
    | 0 => ⟨0, .zero⟩
    | 1 => ⟨0, .one⟩
    | 2 => ⟨1, .neg⟩
    | 3 => ⟨1, .exp⟩
    | 4 => ⟨2, .add⟩
    | 5 => ⟨2, .mul⟩
  left_inv := by
    rintro ⟨_, f⟩
    cases f <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

instance : Encodable (Σ n, expLanguage.Functions n) :=
  Encodable.ofEquiv (Fin 6) expFuncEquivFin

/-- An explicit enumeration of the single relation symbol of `expLanguage`. -/
def expRelEquivFin : (Σ n, expLanguage.Relations n) ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨2, .lt⟩
  left_inv := by
    rintro ⟨_, r⟩
    cases r
    rfl
  right_inv := by
    intro i
    fin_cases i
    rfl

instance : Encodable (Σ n, expLanguage.Relations n) :=
  Encodable.ofEquiv (Fin 1) expRelEquivFin

/-- The real exponential field `ℝ_exp`: the real numbers as an `expLanguage`-structure, with
`0`, `1`, `-`, `+`, `*`, `<` interpreted as usual and `exp` interpreted as `Real.exp`. -/
noncomputable instance : expLanguage.Structure ℝ where
  funMap {n} f := match n, f with
    | _, .zero => fun _ => 0
    | _, .one => fun _ => 1
    | _, .neg => fun x => -x 0
    | _, .exp => fun x => Real.exp (x 0)
    | _, .add => fun x => x 0 + x 1
    | _, .mul => fun x => x 0 * x 1
  RelMap {n} r := match n, r with
    | _, .lt => fun x => x 0 < x 1

/-- The Gödel number of a sentence of a language whose function and relation symbols are
encodable: the sentence is first encoded as a list of symbols using
`FirstOrder.Language.BoundedFormula.listEncode`, and this list is then encoded as a natural
number. -/
def Sentence.godelNumber {L : Language} [Encodable (Σ n, L.Functions n)]
    [Encodable (Σ n, L.Relations n)] (φ : L.Sentence) : ℕ :=
  Encodable.encode (BoundedFormula.listEncode φ)

/-- A theory `T` (in a language with encodable symbols) is *decidable* if the set of Gödel
numbers of the sentences in `T` is a computable set of natural numbers. -/
def Theory.IsDecidable {L : Language} [Encodable (Σ n, L.Functions n)]
    [Encodable (Σ n, L.Relations n)] (T : L.Theory) : Prop :=
  ComputablePred (· ∈ Sentence.godelNumber '' T)

/--
**Tarski's exponential function problem.**
Is the theory of the real numbers with the exponential function decidable?

That is, is the complete first-order theory $\operatorname{Th}(\mathbb{R}_{\exp})$ of the
structure $\mathbb{R}_{\exp} = (\mathbb{R}, +, \cdot, -, <, 0, 1, \exp)$ decidable, in the
sense that the set of Gödel numbers of the sentences true in $\mathbb{R}_{\exp}$ is a computable
set?
-/
theorem tarskis_exponential_function_problem :
    Theory.IsDecidable (expLanguage.completeTheory ℝ) := by
  sorry

end TarskisExponentialFunctionProblem

theorem TarskisExponentialFunctionProblem.tarskis_exponential_function_problem.disproof : ¬ (type_of% @TarskisExponentialFunctionProblem.tarskis_exponential_function_problem) := sorry
