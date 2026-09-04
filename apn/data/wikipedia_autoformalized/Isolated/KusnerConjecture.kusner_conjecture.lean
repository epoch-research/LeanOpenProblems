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
# Kusner conjecture

A set of points in a metric space is *equilateral* (or *equidistant*) if all pairs of distinct
points in it are at the same positive distance from each other. The *equilateral dimension* of the
space is the largest size of such a set.

Let $\ell^1_d$ denote $\mathbb{R}^d$ with the $L^1$ (Manhattan) norm
$\|x\|_1 = |x_1| + \cdots + |x_d|$. Robert B. Kusner conjectured (1983) that at most $2d$ points
of $\ell^1_d$ can be equidistant. The $2d$ vertices $\pm e_i$ of the cross-polytope are pairwise
at $L^1$-distance $2$, so the conjecture says that the equilateral dimension of $\ell^1_d$ is
exactly $2d$. It is known for $d \le 4$, and the best general upper bound is $O(d \log d)$
(Alon–Pudlák).

*References:*
- [Wikipedia, Kusner conjecture](https://en.wikipedia.org/wiki/Kusner_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [R. K. Guy, *An olla-podrida of open problems, often oddly posed*,
  Amer. Math. Monthly **90** (1983), 196–200](https://doi.org/10.2307/2975549)
- [J. Koolen, M. Laurent, A. Schrijver, *Equilateral dimension of the rectilinear space*,
  Des. Codes Cryptogr. **21** (2000), 149–164](https://doi.org/10.1023/A:1008391712305)
- [N. Alon, P. Pudlák, *Equilateral sets in $l_p^n$*,
  Geom. Funct. Anal. **13** (2003), 467–482](https://doi.org/10.1007/s00039-003-0418-7)
-/

namespace KusnerConjecture

/-- `ℓ¹[d]` is $\mathbb{R}^d$ with the $L^1$ (Manhattan) norm, so that
`dist x y = ∑ i, |x i - y i|`. -/
local notation "ℓ¹[" d "]" => PiLp 1 (fun _ : Fin d => ℝ)

/-- **Kusner's conjecture.** For every $d \geq 1$, at most $2d$ points of $\mathbb{R}^d$ can be
equidistant in the $L^1$ (Manhattan) metric: if $S \subseteq \mathbb{R}^d$ and there is some
$r > 0$ with $\|x - y\|_1 = r$ for all distinct $x, y \in S$, then $|S| \leq 2d$.

The hypothesis $d \geq 1$ excludes $\mathbb{R}^0$, a single point, which is a one-element
equidistant set. -/
theorem kusner_conjecture (d : ℕ) (hd : 0 < d) (S : Set ℓ¹[d])
    (hS : ∃ r > 0, S.Pairwise (dist · · = r)) :
    S.encard ≤ 2 * d := by
  sorry

end KusnerConjecture

theorem KusnerConjecture.kusner_conjecture.disproof : ¬ (type_of% @KusnerConjecture.kusner_conjecture) := sorry
