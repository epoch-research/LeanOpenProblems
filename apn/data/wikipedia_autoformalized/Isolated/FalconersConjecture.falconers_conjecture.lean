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
# Falconer's conjecture

Falconer's conjecture states that a compact set in $\mathbb{R}^d$ whose Hausdorff dimension is
strictly greater than $d/2$ must have a distance set of nonzero Lebesgue measure.

*References:*
- [Wikipedia, Falconer's conjecture](https://en.wikipedia.org/wiki/Falconer%27s_conjecture)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Fa85] Falconer, K. J., _On the Hausdorff dimensions of distance sets_.
  Mathematika 32 (1985), no. 2, 206–212.
- [GIOW20] Guth, L., Iosevich, A., Ou, Y. and Wang, H., _On Falconer's distance set problem in
  the plane_. Invent. Math. 219 (2020), no. 3, 779–830.
  [arXiv:1808.09346](https://arxiv.org/abs/1808.09346)
- [DORZ23] Du, X., Ou, Y., Ren, K. and Zhang, R., _New improvement to Falconer distance set
  problem in higher dimensions_. [arXiv:2309.04103](https://arxiv.org/abs/2309.04103)
-/

open MeasureTheory

open scoped ENNReal EuclideanGeometry

namespace FalconersConjecture

/--
**Falconer's conjecture.** Let $d \ge 2$ and let $E \subseteq \mathbb{R}^d$ be a compact set whose
Hausdorff dimension is strictly greater than $d/2$. Then the distance set
$$\Delta(E) = \{\, |x - y| : x, y \in E \,\}$$
of Euclidean distances between pairs of points of $E$ has nonzero (that is, strictly positive)
one-dimensional Lebesgue measure.

Here `dist x y = ‖x - y‖` is the Euclidean distance on `ℝ^d` and `volume` is Lebesgue measure on
`ℝ`. The set is quantified over compact sets, as in the Wikipedia article and the literature on
the problem; Falconer [Fa85] proved the corresponding statement for Borel sets with the larger
threshold $(d+1)/2$. The restriction $d \ge 2$ is implicit in the sources and is needed: in
$\mathbb{R}$ there are compact sets of Hausdorff dimension $1$ whose difference set has Lebesgue
measure zero. The threshold $d/2$ cannot be lowered: for every $s \le d/2$ Falconer's lattice
examples give compact sets of Hausdorff dimension $s$ whose distance set has measure zero.
-/
theorem falconers_conjecture (d : ℕ) (hd : 2 ≤ d) (E : Set (ℝ^d)) (hE : IsCompact E)
    (hdim : (d : ℝ≥0∞) / 2 < dimH E) :
    0 < volume {dist x y | (x ∈ E) (y ∈ E)} := by
  sorry

end FalconersConjecture

theorem FalconersConjecture.falconers_conjecture.disproof : ¬ (type_of% @FalconersConjecture.falconers_conjecture) := sorry
