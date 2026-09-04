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
# Kalai's $3^d$ conjecture

Kalai's $3^d$ conjecture (1989) states that every $d$-dimensional centrally symmetric convex
polytope has at least $3^d$ nonempty faces. The count includes the faces of every dimension
$0, 1, \dots, d$, so the polytope itself is counted, but the empty face is not.

A convex polytope is the convex hull of a finite set of points. It is $d$-dimensional if its
affine span is all of $\mathbb{R}^d$. It is centrally symmetric if $P = -P$; a polytope symmetric
about another centre is a translate of such a $P$, and translating does not change the number of
faces. The nonempty faces of a polytope are exactly its nonempty exposed subsets (`IsExposed`),
i.e. the sets of maximisers over $P$ of a linear functional, where the zero functional gives $P$
itself.

The bound is attained by the $d$-cube, the $d$-crosspolytope and, more generally, by every Hanner
polytope. The conjecture is known for $d \le 4$ and for simplicial polytopes.

*References:*
- [Wikipedia, Kalai's $3^d$ conjecture](https://en.wikipedia.org/wiki/Kalai%27s_3%5Ed_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- G. Kalai, *The number of faces of centrally-symmetric polytopes*, Graphs and Combinatorics 5
  (1989), 389–391.
- R. Sanyal, A. Werner, G. M. Ziegler, *On Kalai's conjectures concerning centrally symmetric
  polytopes*, Discrete & Computational Geometry 41 (2009), 183–198,
  [arXiv:0708.3661](https://arxiv.org/abs/0708.3661) (Conjecture A).
-/

open scoped EuclideanGeometry Pointwise

namespace Kalais3dConjecture

/-- **Kalai's $3^d$ conjecture.** Let $P \subseteq \mathbb{R}^d$ be a convex polytope (the convex
hull of a finite set) that is full-dimensional (its affine span is $\mathbb{R}^d$) and centrally
symmetric ($P = -P$). Then $P$ has at least $3^d$ nonempty faces, counting the faces of all
dimensions $0, 1, \dots, d$: the polytope $P$ itself is counted and the empty face is not.

The nonempty faces of $P$ are formalised as its nonempty exposed subsets, i.e. the nonempty sets
$\{x \in P \mid \forall y \in P,\ \ell(y) \le \ell(x)\}$ for a linear functional $\ell$. -/
@[category research open, AMS 52]
theorem kalais_3d_conjecture (d : ℕ) (P : Set (ℝ^d))
    (hP : ∃ S : Finset (ℝ^d), P = convexHull ℝ ↑S)
    (hdim : affineSpan ℝ P = ⊤) (hsymm : P = -P) :
    3 ^ d ≤ {F | IsExposed ℝ P F ∧ F.Nonempty}.ncard := by
  sorry

end Kalais3dConjecture
