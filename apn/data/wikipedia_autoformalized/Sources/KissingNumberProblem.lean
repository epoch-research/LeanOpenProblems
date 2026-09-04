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
# The kissing number problem

The kissing number $\kappa(n)$ of $n$-dimensional Euclidean space is the greatest number of
non-overlapping unit spheres that can be arranged so that each of them touches a common unit
sphere. Two spheres are non-overlapping if their interiors are disjoint; touching is allowed.

Placing the central sphere at the origin, a unit sphere touching it has centre $c$ with
$\|c\| = 2$, and two such spheres are non-overlapping exactly when their centres are at distance
at least $2$. Rescaling by $1/2$, a kissing configuration of $N$ spheres is a family of $N$ unit
vectors $x_1, \dots, x_N$ with $\|x_i - x_j\| \ge 1$ for all $i \ne j$ (equivalently
$\langle x_i, x_j \rangle \le 1/2$), and $\kappa(n)$ is the largest such $N$. This is the
formulation in the "Mathematical statement" section of the Wikipedia article.

The kissing number is known exactly only for $n \in \{1, 2, 3, 4, 8, 24\}$. The kissing number
problem asks for $\kappa(n)$ in the remaining dimensions. For $n = 5, 6, 7$ the arrangements
with the highest known kissing numbers are the optimal lattice arrangements, given by the
minimal vectors of the root lattices $D_5$, $E_6$ and $E_7$, with $40$, $72$ and $126$ spheres
respectively. These are conjectured to be optimal, but the existence of a non-lattice
arrangement with a higher kissing number has not been excluded. The best known upper bounds are
$\kappa(5) \le 44$, $\kappa(6) \le 77$ and $\kappa(7) \le 134$.

*References:*
- [Wikipedia, Kissing number](https://en.wikipedia.org/wiki/kissing_number_problem)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- H. Cohn, A. Li, *Improved kissing numbers in seventeen through twenty-one dimensions*,
  [arXiv:2411.04916](https://arxiv.org/abs/2411.04916). Table 1 lists the best known bounds.
- H. D. Mittelmann, F. Vallentin, *High accuracy semidefinite programming bounds for kissing
  numbers*, Experiment. Math. 19 (2010), 175–179,
  [arXiv:0902.1105](https://arxiv.org/abs/0902.1105)
-/

open scoped EuclideanGeometry

namespace KissingNumberProblem

/--
A family `x : Fin N → ℝ^n` is a *kissing configuration* of `N` spheres in $\mathbb{R}^n$ if its
points are unit vectors with pairwise distances at least $1$.

The point `x i` is the point of tangency of the `i`-th outer unit sphere with the central unit
sphere centred at the origin: the `i`-th outer sphere has centre `2 • x i`, and two outer unit
spheres have disjoint interiors exactly when their centres are at distance at least `2`, i.e.
when `1 ≤ dist (x i) (x j)`. The pairwise condition forces `x` to be injective, so `N` is the
number of spheres.
-/
def IsKissingConfiguration {n N : ℕ} (x : Fin N → ℝ^n) : Prop :=
  (∀ i, ‖x i‖ = 1) ∧ Pairwise fun i j => 1 ≤ dist (x i) (x j)

/--
The *kissing number* $\kappa(n)$ of $\mathbb{R}^n$: the greatest number of non-overlapping unit
spheres that can simultaneously touch a central unit sphere in $\mathbb{R}^n$.

The set of sizes of kissing configurations contains `0` and is bounded above (by compactness of
the unit sphere), so this supremum is attained.
-/
noncomputable def kissingNumber (n : ℕ) : ℕ :=
  sSup {N | ∃ x : Fin N → ℝ^n, IsKissingConfiguration x}

/--
**The kissing number problem in dimension 5.**

In five dimensions the arrangement with the highest known kissing number is the optimal lattice
arrangement, given by the $40$ minimal vectors of the root lattice $D_5$, so $\kappa(5) \ge 40$.
The existence of a non-lattice arrangement with a higher kissing number has not been excluded;
the best known upper bound is $\kappa(5) \le 44$. The conjecture is that the $D_5$ arrangement
is optimal, i.e. $\kappa(5) = 40$.
-/
@[category research open, AMS 52]
theorem kissing_number_problem.parts.i : kissingNumber 5 = 40 := by
  sorry

/--
**The kissing number problem in dimension 6.**

In six dimensions the arrangement with the highest known kissing number is the optimal lattice
arrangement, given by the $72$ minimal vectors of the root lattice $E_6$, so $\kappa(6) \ge 72$.
The existence of a non-lattice arrangement with a higher kissing number has not been excluded;
the best known upper bound is $\kappa(6) \le 77$. The conjecture is that the $E_6$ arrangement
is optimal, i.e. $\kappa(6) = 72$.
-/
@[category research open, AMS 52]
theorem kissing_number_problem.parts.ii : kissingNumber 6 = 72 := by
  sorry

/--
**The kissing number problem in dimension 7.**

In seven dimensions the arrangement with the highest known kissing number is the optimal lattice
arrangement, given by the $126$ minimal vectors of the root lattice $E_7$, so $\kappa(7) \ge 126$.
The existence of a non-lattice arrangement with a higher kissing number has not been excluded;
the best known upper bound is $\kappa(7) \le 134$. The conjecture is that the $E_7$ arrangement
is optimal, i.e. $\kappa(7) = 126$.
-/
@[category research open, AMS 52]
theorem kissing_number_problem.parts.iii : kissingNumber 7 = 126 := by
  sorry

end KissingNumberProblem
