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
# Diophantine $m$-tuples

A **Diophantine $m$-tuple** is a set of $m$ distinct positive integers
$\{a_1, \dots, a_m\}$ such that $a_i a_j + 1$ is a perfect square for every
$i \neq j$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Diophantine_quintuple)
- [Du16] Dujella, Andrej,
  [*What is... a Diophantine m-tuple?*](https://www.ams.org/journals/notices/201607/rnoti-p772.pdf),
  Notices Amer. Math. Soc. 63 (2016), 772--774.
- [Du] Dujella, Andrej,
  [*Diophantine quintuple conjecture*](https://web.math.pmf.unizg.hr/~duje/quint.html).
- [HTZ19] He, Bo, Togbé, Alain and Ziegler, Volker,
  [*There is no Diophantine quintuple*](https://arxiv.org/abs/1610.04020),
  Trans. Amer. Math. Soc. 371 (2019), 6665--6709.
- [BD69] Baker, Alan and Davenport, Harold, The equations $3x^2-2=y^2$ and $8x^2-7=z^2$.
  Quart. J. Math. Oxford Ser. (2) 20 (1969), 129--137.
- [Gi99] Gibbs, Philip,
  [*Some rational Diophantine sextuples*](https://arxiv.org/abs/math/9902081), (1999).
-/

namespace DiophantineTuple

variable {R : Type*} [Semiring R]

/--
A finite set `s` is a **Diophantine tuple** if each element is nonzero and the product
of any two distinct elements is one less than a perfect square.

We define this for all semirings and specialize to the integral and rational cases in this file;
these are the most common in the literature. Note that the cases of `ℕ` and `ℕ+` are
mathematically equivalent.
-/
def IsDiophantineTuple (s : Finset R) : Prop :=
  (∀ x ∈ s, x ≠ 0) ∧
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → IsSquare (x * y + 1)

/-- An **integral Diophantine tuple** is a Diophantine tuple of positive integers. -/
abbrev IsIntegralDiophantineTuple (s : Finset ℕ) : Prop := IsDiophantineTuple (R := ℕ) s

/-- A **rational Diophantine tuple** is a Diophantine tuple of nonzero rationals. -/
abbrev IsRationalDiophantineTuple (s : Finset ℚ) : Prop := IsDiophantineTuple (R := ℚ) s

/-
Conjectures / theorems about existence of integral Diophantine m-tuples for various values of m
-/

/--
The set of integral Diophantine 4-tuples.
-/
def integralDiophantine4Tuple : Set (Finset ℕ) :=
  { s | IsIntegralDiophantineTuple s ∧ s.card = 4 }

/--
The statement that there is no integral Diophantine 5-tuple.
-/
abbrev NoIntegralDiophantineFiveTuple := ¬∃ t, IsIntegralDiophantineTuple t ∧ t.card = 5

/-
Conjectures / theorems about extending integral Diophantine tuples
-/

/--
Given an integral Diophantine 3-tuple, there is a standard way to extend it to a 4-tuple by
adjoining the value of this function. This is $d_+$ in [Du].

Note that when $\{a, b, c\}$ is a Diophantine tuple, each factor under the square root
(e.g. $ab + 1$) is a perfect square.
-/
def regularExtension (a b c : ℕ) : ℕ :=
  a + b + c + 2 * a * b * c + 2 * Nat.sqrt ((a * b + 1) * (a * c + 1) * (b * c + 1))

/--
The property that the Diophantine 3-tuple $\{a, b, c\}$ extends to a 4-tuple $\{a, b, c, d\}$
with $d > \max(a, b, c)$ only via `regularExtension`.
-/
def HasUniqueExtension (a b c : ℕ) : Prop :=
  (IsIntegralDiophantineTuple { a, b, c }) ∧
  ∀ d : ℕ, (IsIntegralDiophantineTuple { a, b, c, d }) → max a (max b c) < d →
    d = regularExtension a b c

/--
The statement that every integral Diophantine triple of three distinct elements has a unique
extension by a larger element.
-/
abbrev HasUniqueExtensionOfForall :=
  ∀ a b c : ℕ, ({a, b, c} : Finset ℕ).card = 3 → IsIntegralDiophantineTuple {a, b, c} →
    HasUniqueExtension a b c

/-
Theorems and conjectures about the rational case
-/

/--
Does there exist a rational Diophantine 7-tuple? [Du16]
-/
theorem rational_7_tuple :
    ∃ t, IsRationalDiophantineTuple t ∧ t.card = 7 := by
  sorry

end DiophantineTuple

theorem DiophantineTuple.rational_7_tuple.disproof : ¬ (type_of% @DiophantineTuple.rational_7_tuple) := sorry
