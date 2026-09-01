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
# Number of ways to express $n$ as sum of square, pentagonal, and hexagonal numbers

$$a(n) = |\{(x, y, z) \in \mathbb{N}^3 : x^2 + p_5(y) + p_6(z) = n\}|$$

*References:*
- [A160324](https://oeis.org/A160324)-/

namespace OeisA160324

/-- $p_k(x) = \frac{(k-2)x(x-1)}{2} + x$ is the $x$-th $k$-gonal number. -/
def polygonalNumber (k x : ℕ) : ℕ :=
  (k - 2) * (x * (x - 1) / 2) + x

/-- $p_5(y) = \frac{3y^2 - y}{2}$ is the $y$-th pentagonal number. -/
def pentagonal (y : ℕ) : ℕ := polygonalNumber 5 y

/-- $p_6(z) = 2z^2 - z$ is the $z$-th hexagonal number. -/
def hexagonal (z : ℕ) : ℕ := polygonalNumber 6 z

/-- Number of representations of $n$ as sum of square, pentagonal, and hexagonal numbers. -/
def a (n : ℕ) : ℕ :=
  let max_coord_bound := n.sqrt + 2
  ∑ x ∈ Finset.range max_coord_bound,
    ∑ y ∈ Finset.range max_coord_bound,
      ∑ z ∈ Finset.range max_coord_bound,
        if x ^ 2 + pentagonal y + hexagonal z = n then 1 else 0

/--
In April 2009, _Zhi-Wei Sun_ conjectured that $a(n) > 0$ for every $n = 0, 1, 2, 3, \dots$.
-/
theorem conjecture1 (n : ℕ) : 0 < a n := by
  sorry

end OeisA160324

theorem OeisA160324.conjecture1.disproof : ¬ (type_of% @OeisA160324.conjecture1) := sorry
