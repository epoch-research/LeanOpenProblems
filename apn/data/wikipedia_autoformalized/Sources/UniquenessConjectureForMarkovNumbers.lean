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
# Uniqueness conjecture for Markov numbers

A **Markov triple** is a triple $(x, y, z)$ of positive integers that solves the Markov
Diophantine equation $x^2 + y^2 + z^2 = 3xyz$. A **Markov number** is a positive integer that
appears in some Markov triple. Permuting the entries of a Markov triple gives another Markov
triple, so one may **normalize** a triple by requiring $x \le y \le z$.

The **uniqueness conjecture** (or *unicity conjecture*), remarked by Frobenius in 1913, states
that every Markov number is the largest number in exactly one normalized solution to the Markov
Diophantine equation. Equivalently, if $(a, b, c)$ and $(a', b', c)$ are Markov triples with
$a \le b \le c$ and $a' \le b' \le c$, then $a = a'$ and $b = b'$.

*References:*
- [Wikipedia, Markov number](https://en.wikipedia.org/wiki/Markov_number%23Other_properties)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Fr13] Frobenius, G., *Über die Markoffschen Zahlen*, S.-B. Preuss. Akad. Wiss. (1913),
  458--487.
- [Ai13] Aigner, Martin, *Markov's Theorem and 100 Years of the Uniqueness Conjecture*,
  Springer, Cham (2013).
- [Zh07] Zhang, Ying, *Congruence and Uniqueness of Certain Markov Numbers*,
  Acta Arith. 128 (2007), 295--301. [arXiv:math/0612620](https://arxiv.org/abs/math/0612620)
-/

namespace UniquenessConjectureForMarkovNumbers

/-- A triple $(x, y, z)$ of positive integers is a **Markov triple** if it is a solution to the
Markov Diophantine equation $x^2 + y^2 + z^2 = 3xyz$. -/
def IsMarkovTriple (x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z

/-- A Markov triple $(x, y, z)$ is **normalized** if $x \le y \le z$. In particular $z$ is its
largest number. -/
def IsNormalizedMarkovTriple (x y z : ℕ) : Prop :=
  IsMarkovTriple x y z ∧ x ≤ y ∧ y ≤ z

/-- A **Markov number** is a positive integer that appears in some Markov triple. -/
def IsMarkovNumber (m : ℕ) : Prop :=
  ∃ x y z, IsMarkovTriple x y z ∧ (m = x ∨ m = y ∨ m = z)

/-- $(1, 1, 1)$ is a normalized Markov triple. -/
@[category test, AMS 11]
theorem isNormalizedMarkovTriple_one_one_one : IsNormalizedMarkovTriple 1 1 1 := by
  norm_num [IsNormalizedMarkovTriple, IsMarkovTriple]

/-- $(1, 2, 5)$ is a normalized Markov triple. -/
@[category test, AMS 11]
theorem isNormalizedMarkovTriple_one_two_five : IsNormalizedMarkovTriple 1 2 5 := by
  norm_num [IsNormalizedMarkovTriple, IsMarkovTriple]

/-- $(5, 2, 1)$ is a Markov triple, but it is not normalized. -/
@[category test, AMS 11]
theorem not_isNormalizedMarkovTriple_five_two_one :
    IsMarkovTriple 5 2 1 ∧ ¬ IsNormalizedMarkovTriple 5 2 1 := by
  norm_num [IsNormalizedMarkovTriple, IsMarkovTriple]

/-- $(1, 2, 2)$ is not a Markov triple. -/
@[category test, AMS 11]
theorem not_isMarkovTriple_one_two_two : ¬ IsMarkovTriple 1 2 2 := by
  norm_num [IsMarkovTriple]

/-- $13$ is a Markov number, as it appears in the Markov triple $(1, 5, 13)$. -/
@[category test, AMS 11]
theorem isMarkovNumber_thirteen : IsMarkovNumber 13 :=
  ⟨1, 5, 13, by norm_num [IsMarkovTriple], by simp⟩

/-- $0$ is not a Markov number: the entries of a Markov triple are positive, so the trivial
solution $(0, 0, 0)$ is excluded. -/
@[category test, AMS 11]
theorem not_isMarkovNumber_zero : ¬ IsMarkovNumber 0 := by
  rintro ⟨x, y, z, ⟨hx, hy, hz, -⟩, h⟩
  omega

/-- **Uniqueness conjecture for Markov numbers** (Frobenius, 1913).
Every Markov number $c$ is the largest number in exactly one normalized solution
$(a, b, c)$ with $a \le b \le c$ of the Markov Diophantine equation $a^2 + b^2 + c^2 = 3abc$.
That is, for a given Markov number $c$ there is exactly one pair $(a, b)$ of positive integers
with $a \le b \le c$ and $a^2 + b^2 + c^2 = 3abc$. -/
@[category research open, AMS 11]
theorem uniqueness_conjecture_for_markov_numbers (c : ℕ) (hc : IsMarkovNumber c) :
    ∃! p : ℕ × ℕ, IsNormalizedMarkovTriple p.1 p.2 c := by
  sorry

/-- The existence half of the uniqueness conjecture: every Markov number is the largest
number of some normalized Markov triple. This is elementary; it follows by descending
along the Markov tree. -/
@[category textbook, AMS 11]
theorem uniqueness_conjecture_for_markov_numbers.variants.existence (c : ℕ)
    (hc : IsMarkovNumber c) : ∃ a b, IsNormalizedMarkovTriple a b c := by
  sorry

/-- **The Unicity Conjecture**, as stated in [Zh07]: suppose $(a, b, c)$ and $(a', b', c)$
are Markov triples with $a \le b \le c$ and $a' \le b' \le c$. Then $a = a'$ and $b = b'$. -/
@[category research open, AMS 11]
theorem uniqueness_conjecture_for_markov_numbers.variants.frobenius (a b a' b' c : ℕ)
    (h : IsNormalizedMarkovTriple a b c) (h' : IsNormalizedMarkovTriple a' b' c) :
    a = a' ∧ b = b' := by
  sorry

end UniquenessConjectureForMarkovNumbers
