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
# Generalized star height problem

A *generalized regular expression* over an alphabet $A$ is built from $\emptyset$, $\varepsilon$
and the letters $a \in A$ using union, concatenation, Kleene star and a built-in complement
operator. Its *star height* is the maximal nesting depth of Kleene stars: constants and letters
have star height $0$, union, concatenation and complement do not increase it, and $E^*$ has star
height $h(E) + 1$. The *generalized star height* of a regular language is the minimum star height
of a generalized regular expression denoting it.

The generalized star height problem asks whether all regular languages can be expressed using
generalized regular expressions with a limited nesting depth of Kleene stars, that is, whether
there is a uniform bound $k$ such that every regular language over every finite alphabet has
generalized star height at most $k$. More specifically, it is open whether a nesting depth of
more than $1$ is ever required: no regular language of generalized star height at least $2$ is
known.

Mathlib's `RegularExpression` has no complement operator, so this file introduces the bespoke
inductive type `GeneralizedRegularExpression` together with its language `matches'` and its
`starHeight`. Regular languages are Mathlib's `Language.IsRegular`. Alphabets are required to be
finite, as usual in formal language theory: over an infinite alphabet a finite automaton can
treat infinitely many letters alike, whereas an expression only mentions finitely many letters.

*References:*
- [Wikipedia: Generalized star height problem](https://en.wikipedia.org/wiki/Generalized_star_height_problem)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- J.-E. Pin, H. Straubing, D. Thérien,
  [*Some results on the generalized star-height problem*](https://www.irif.fr/~jep//PDF/StarHeight.pdf),
  Information and Computation 101 (1992), 219--250.
-/

open scoped Computability

namespace GeneralizedStarHeightProblem

/-- Generalized regular expressions over the alphabet `α`: regular expressions with a built-in
complement operator. The constructors mirror Mathlib's `RegularExpression`.
* `zero` denotes the empty language $\emptyset$.
* `epsilon` denotes the language $\{\varepsilon\}$ containing only the empty word.
* `char a` denotes the language $\{a\}$ containing only the one-letter word `a`.
* `plus P Q` denotes the union of the languages of `P` and `Q`.
* `comp P Q` denotes the concatenation of the languages of `P` and `Q`.
* `star P` denotes the Kleene star of the language of `P`.
* `compl P` denotes the complement (in the set of all words over `α`) of the language of `P`. -/
inductive GeneralizedRegularExpression (α : Type*) : Type _
  | zero : GeneralizedRegularExpression α
  | epsilon : GeneralizedRegularExpression α
  | char : α → GeneralizedRegularExpression α
  | plus : GeneralizedRegularExpression α → GeneralizedRegularExpression α →
      GeneralizedRegularExpression α
  | comp : GeneralizedRegularExpression α → GeneralizedRegularExpression α →
      GeneralizedRegularExpression α
  | star : GeneralizedRegularExpression α → GeneralizedRegularExpression α
  | compl : GeneralizedRegularExpression α → GeneralizedRegularExpression α

namespace GeneralizedRegularExpression

variable {α : Type*}

/-- The language denoted by a generalized regular expression.

Not named `matches` since that is a reserved word. -/
def matches' : GeneralizedRegularExpression α → Language α
  | zero => 0
  | epsilon => 1
  | char a => {[a]}
  | plus P Q => P.matches' + Q.matches'
  | comp P Q => P.matches' * Q.matches'
  | star P => P.matches'∗
  | compl P => (P.matches')ᶜ

/-- The star height of a generalized regular expression: the maximal nesting depth of Kleene
stars. Constants and letters have star height `0`; union, concatenation and complement do not
increase the star height; a Kleene star increases it by one. -/
def starHeight : GeneralizedRegularExpression α → ℕ
  | zero => 0
  | epsilon => 0
  | char _ => 0
  | plus P Q => max P.starHeight Q.starHeight
  | comp P Q => max P.starHeight Q.starHeight
  | star P => P.starHeight + 1
  | compl P => P.starHeight

/-- The embedding of ordinary regular expressions into generalized regular expressions. -/
def ofRegularExpression : RegularExpression α → GeneralizedRegularExpression α
  | .zero => zero
  | .epsilon => epsilon
  | .char a => char a
  | .plus P Q => plus (ofRegularExpression P) (ofRegularExpression Q)
  | .comp P Q => comp (ofRegularExpression P) (ofRegularExpression Q)
  | .star P => star (ofRegularExpression P)

end GeneralizedRegularExpression

/--
**Generalized star height problem, nesting depth one.** Is a nesting depth of Kleene stars of
more than $1$ ever required? That is, is there a regular language $L$ over some finite alphabet
such that every generalized regular expression denoting $L$ has star height at least $2$?

A positive answer, `answer(True)`, means that some regular language has generalized star height
at least $2$; a negative answer, `answer(False)`, means that every regular language over every
finite alphabet has generalized star height at most $1$, which is the form in which Pin,
Straubing and Thérien state the problem.
-/
theorem generalized_star_height_problem.variants.height_one :
    ∃ (α : Type) (_ : Finite α) (L : Language α), L.IsRegular ∧
      ∀ e : GeneralizedRegularExpression α, e.matches' = L → 1 < e.starHeight := by
  sorry

end GeneralizedStarHeightProblem

theorem GeneralizedStarHeightProblem.generalized_star_height_problem.variants.height_one.disproof : ¬ (type_of% @GeneralizedStarHeightProblem.generalized_star_height_problem.variants.height_one) := sorry
