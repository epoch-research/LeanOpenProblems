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
# Mahler's conjecture

Mahler's conjecture on the product of the volumes of a centrally symmetric convex body and
its polar.

A *convex body* in $\mathbb{R}^n$ is a compact convex set with nonempty interior. It is
*centrally symmetric* if $K = -K$. Its *polar body* is
$K^\circ = \{x \in \mathbb{R}^n \mid \langle x, y \rangle \le 1 \text{ for all } y \in K\}$,
and the *Mahler volume* of $K$ is $\operatorname{vol}(K) \cdot \operatorname{vol}(K^\circ)$.
Mahler's conjecture states that the Mahler volume of every centrally symmetric convex body in
$\mathbb{R}^n$ is at least $4^n / n!$, the Mahler volume of the cube $[-1, 1]^n$ (whose polar
body is the cross-polytope). The conjecture is known for $n \le 3$ and open for $n \ge 4$.

*References:*
- [Wikipedia, Mahler volume](https://en.wikipedia.org/wiki/Mahler_volume)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [IS20] H. Iriyeh, M. Shibata, *Symmetric Mahler's conjecture for the volume product in the
  3-dimensional case*, Duke Math. J. 169 (2020), 1077–1134.
  [arXiv:1706.01749](https://arxiv.org/abs/1706.01749)
- [Ma39] K. Mahler, *Ein Minimalproblem für konvexe Polygone*, Mathematica (Zutphen) B 7
  (1939), 118–127.
-/

open MeasureTheory

open scoped ENNReal EuclideanGeometry InnerProductSpace Pointwise

namespace MahlersConjecture

/--
The polar body of a set `K ⊆ ℝⁿ` (with respect to the origin):
$K^\circ = \{x \in \mathbb{R}^n \mid \langle x, y \rangle \le 1 \text{ for all } y \in K\}$.

Mathlib's `LinearMap.polar` is the *absolute* polar (defined by `|⟪x, y⟫| ≤ 1`); for centrally
symmetric `K` the two coincide, see `MahlersConjecture.polarBody_eq_polar`.
-/
def polarBody {n : ℕ} (K : Set (ℝ^n)) : Set (ℝ^n) :=
  {x | ∀ y ∈ K, ⟪x, y⟫_ℝ ≤ 1}

/--
**Mahler's conjecture** (symmetric case). Let $n \ge 1$ and let $K \subseteq \mathbb{R}^n$ be a
centrally symmetric convex body, i.e. a compact convex set with nonempty interior such that
$K = -K$. Let $K^\circ = \{x \mid \langle x, y \rangle \le 1 \text{ for all } y \in K\}$ be its
polar body. Then the product of the volumes of $K$ and $K^\circ$ satisfies
$$\operatorname{vol}(K) \cdot \operatorname{vol}(K^\circ) \ge \frac{4^n}{n!},$$
the value attained by the cube $[-1, 1]^n$ (whose polar body is the cross-polytope).

The conjecture is known for $n \le 3$ (Mahler for $n = 2$ [Ma39], Iriyeh and Shibata for
$n = 3$ [IS20]) and open for $n \ge 4$.
-/
theorem mahlers_conjecture (n : ℕ) (hn : 1 ≤ n) (K : Set (ℝ^n)) (hK_compact : IsCompact K)
    (hK_convex : Convex ℝ K) (hK_int : (interior K).Nonempty) (hK_symm : -K = K) :
    (4 : ℝ≥0∞) ^ n / n.factorial ≤ volume K * volume (polarBody K) := by
  sorry

end MahlersConjecture

theorem MahlersConjecture.mahlers_conjecture.disproof : ¬ (type_of% @MahlersConjecture.mahlers_conjecture) := sorry
