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
# Big-line-big-clique conjecture

The big-line-big-clique conjecture of Kára, Pór and Wood (2005) states that every
sufficiently large finite set of points in the Euclidean plane contains either many
collinear points (a "big line") or many mutually visible points (a "big clique" in the
visibility graph).

Two distinct points $p, q$ of a point set $P$ are *visible* with respect to $P$ if no point
of $P$ lies in the open line segment between $p$ and $q$. In Lean this is `IsVisible ℝ P p q`.

The conjecture is only stated for finite point sets: Pór and Wood showed that it fails for
infinite point sets (there is a countably infinite planar point set with no $4$ collinear
points and no $3$ pairwise visible points).

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Big-line-big-clique_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [KPW05] Kára, Jan; Pór, Attila; Wood, David R., *On the chromatic number of the visibility
  graph of a set of points in the plane*. Discrete Comput. Geom. 34 (2005), 497–506.
- [PW10] Pór, Attila; Wood, David R., *The big-line-big-clique conjecture is false for infinite
  point sets*. [arXiv:1008.2988](https://arxiv.org/abs/1008.2988)
-/

open scoped EuclideanGeometry

namespace BigLineBigCliqueConjecture

/--
**Big-line-big-clique conjecture** (Kára, Pór, Wood [KPW05]).

For all integers $k \geq 2$ and $\ell \geq 2$ there is an integer $n$ such that every finite set
$P$ of at least $n$ points in the plane $\mathbb{R}^2$ contains
* $\ell$ collinear points (a "big line"), or
* $k$ pairwise visible points (a "big clique"),

where two distinct points $p, q \in P$ are *visible* with respect to $P$ if no point of $P$ lies
in the open line segment between $p$ and $q$.

The cases $k \leq 1$ or $\ell \leq 1$ are trivial, so this is equivalent to the version for all
positive integers $k, \ell$. The conjecture is known to hold for $k \leq 5$ or $\ell \leq 3$, and
is open for $k = 6$ or $\ell = 4$.
-/
theorem big_line_big_clique_conjecture (k ℓ : ℕ) (hk : 2 ≤ k) (hℓ : 2 ≤ ℓ) :
    ∃ n : ℕ, ∀ P : Finset ℝ², n ≤ P.card →
      (∃ L ⊆ P, L.card = ℓ ∧ Collinear ℝ (L : Set ℝ²)) ∨
      (∃ Q ⊆ P, Q.card = k ∧ (Q : Set ℝ²).Pairwise (IsVisible ℝ (P : Set ℝ²))) := by
  sorry

end BigLineBigCliqueConjecture

theorem BigLineBigCliqueConjecture.big_line_big_clique_conjecture.disproof : ¬ (type_of% @BigLineBigCliqueConjecture.big_line_big_clique_conjecture) := sorry
