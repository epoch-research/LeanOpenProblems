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

/-- A finite set of points has finitely many ordinary lines. -/
@[category API, AMS 51 52]
theorem ordinaryLines_finite {P : Set ℝ²} (hP : P.Finite) : (ordinaryLines P).Finite := by
  refine ((hP.prod hP).image fun pq ↦ line[ℝ, pq.1, pq.2]).subset ?_
  rintro L ⟨p, hp, q, hq, -, rfl, -⟩
  exact ⟨(p, q), ⟨hp, hq⟩, rfl⟩

/-- The line through two distinct points is an ordinary line of the pair. -/
@[category test, AMS 51 52]
theorem mem_ordinaryLines_pair {p q : ℝ²} (hpq : p ≠ q) :
    line[ℝ, p, q] ∈ ordinaryLines {p, q} := by
  refine ⟨p, by simp, q, by simp, hpq, rfl, ?_⟩
  rw [Set.inter_eq_right.mpr, Set.ncard_pair hpq]
  rintro x (rfl | rfl)
  · exact left_mem_affineSpan_pair ℝ _ _
  · exact right_mem_affineSpan_pair ℝ _ _

/-- The empty set of points has no ordinary lines. -/
@[category test, AMS 51 52]
theorem ordinaryLines_empty : ordinaryLines ∅ = ∅ := by
  ext L
  simp [ordinaryLines]

/-- A set of at least three collinear points spans no ordinary line. This is the degenerate
case excluded by the hypothesis of the Dirac–Motzkin conjecture. -/
@[category test, AMS 51 52]
theorem ordinaryLines_eq_empty_of_collinear (S : Finset ℝ²) (hS : Collinear ℝ (S : Set ℝ²))
    (hcard : 3 ≤ S.card) : ordinaryLines S = ∅ := by
  ext L
  simp only [ordinaryLines, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨p, hp, q, hq, hpq, rfl, h2⟩
  have hsub : (S : Set ℝ²) ⊆ (line[ℝ, p, q] : Set ℝ²) := fun r hr =>
    hS.mem_affineSpan_of_mem_of_ne hp hq hr hpq
  rw [Set.inter_eq_right.mpr hsub, Set.ncard_coe_finset] at h2
  omega

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
@[category research open, AMS 51 52]
theorem dirac_motzkin_conjecture (P : Finset ℝ²) (hP : ¬ Collinear ℝ (P : Set ℝ²)) :
    P.card / 2 ≤ (ordinaryLines P).ncard := by
  sorry

end DiracMotzkinConjecture
