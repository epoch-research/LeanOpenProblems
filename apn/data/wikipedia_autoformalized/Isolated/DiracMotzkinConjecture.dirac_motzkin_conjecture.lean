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
# Dirac–Motzkin conjecture

Let $P$ be a finite set of $n$ points in the Euclidean plane $\mathbb{R}^2$, not all on one
line. A line is *ordinary* (for $P$) if it contains exactly two points of $P$. The
Sylvester–Gallai theorem says that $P$ spans at least one ordinary line. The Dirac–Motzkin
conjecture (Dirac, 1951) states that $P$ always spans at least $\lfloor n/2 \rfloor$ ordinary
lines.

The bound is attained for all even $n > 4$ by constructions of Böröczky, and for odd $n$ by the
Kelly–Moser configuration ($n = 7$, three ordinary lines) and the McKee configuration ($n = 13$,
six ordinary lines). Green and Tao [GT13] proved the conjecture for all sufficiently large $n$
(in the stronger form "at least $n/2$ ordinary lines"); for general $n$ it remains open.

*References:*
- [Wikipedia, Sylvester–Gallai theorem, *The number of ordinary lines*](https://en.wikipedia.org/wiki/Sylvester%E2%80%93Gallai_theorem%23The_number_of_ordinary_lines)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [GT13] Green, B., Tao, T. *On sets defining few ordinary lines*. Discrete Comput. Geom. 50
  (2013). [arXiv:1208.4714](https://arxiv.org/abs/1208.4714)
-/

namespace DiracMotzkinConjecture

open EuclideanGeometry

/--
The set of *ordinary lines* of a set `P` of points in the plane: the lines spanned by two
distinct points of `P` that contain exactly two points of `P`. Lines are represented as affine
subspaces of `ℝ²`.
-/
def ordinaryLines (P : Set ℝ²) : Set (AffineSubspace ℝ ℝ²) :=
  {L | ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ L = line[ℝ, p, q] ∧ (↑L ∩ P).ncard = 2}

/--
**Dirac–Motzkin conjecture.** Every finite set $P$ of $n$ points in the Euclidean plane
$\mathbb{R}^2$, not all on one line, spans at least $\lfloor n/2 \rfloor$ ordinary lines, that is,
lines containing exactly two points of $P$. Here `P.card / 2` is natural number division, so it
equals $\lfloor n/2 \rfloor$.

The hypothesis that the points are not all collinear excludes the degenerate case of a
collinear set, which spans no ordinary line at all; in particular it forces $n \geq 3$.
The floor is essential: the Kelly–Moser configuration ($n = 7$) has exactly $3$ ordinary lines
and the McKee configuration ($n = 13$) has exactly $6$.
-/
theorem dirac_motzkin_conjecture (P : Finset ℝ²) (hP : ¬ Collinear ℝ (P : Set ℝ²)) :
    P.card / 2 ≤ (ordinaryLines P).ncard := by
  sorry

end DiracMotzkinConjecture

theorem DiracMotzkinConjecture.dirac_motzkin_conjecture.disproof : ¬ (type_of% @DiracMotzkinConjecture.dirac_motzkin_conjecture) := sorry
