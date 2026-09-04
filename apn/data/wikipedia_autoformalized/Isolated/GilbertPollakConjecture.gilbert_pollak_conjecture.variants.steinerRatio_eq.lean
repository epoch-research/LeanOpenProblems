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
# Gilbert–Pollak conjecture

Let $S$ be a finite set of points in the Euclidean plane. The *Euclidean minimum spanning tree*
of $S$ is a shortest tree of straight line segments connecting the points of $S$ whose vertices
all belong to $S$. A *Steiner minimum tree* of $S$ is a shortest tree of straight line segments
connecting the points of $S$ that may also use finitely many additional vertices, called
*Steiner points*. Its length is the infimum of the minimum spanning tree lengths of the finite
supersets of $S$.

The *Steiner ratio* of the Euclidean plane is the infimum, over all finite point sets $S$ with at
least two points, of the ratio of the length of a Steiner minimum tree of $S$ to the length of a
Euclidean minimum spanning tree of $S$. (The Wikipedia article on the conjecture uses the
reciprocal convention: the supremum of the ratio of the minimum spanning tree length to the
Steiner minimum tree length, whose conjectured value is $2/\sqrt{3}$.)

The three vertices of an equilateral triangle of unit side length have a minimum spanning tree of
length $2$ and a Steiner minimum tree of length $\sqrt{3}$, so the Steiner ratio is at most
$\sqrt{3}/2$. The Gilbert–Pollak conjecture (1968) states that this example is the worst case:
the Steiner ratio of the Euclidean plane equals $\sqrt{3}/2$. Equivalently, for every finite set
of points in the Euclidean plane, the Euclidean minimum spanning tree is no longer than
$2/\sqrt{3}$ times the Steiner minimum tree. A proof published by Du and Hwang in 1990 was later
found to contain a serious gap, and the conjecture is considered open.

*References:*
- [Wikipedia, Gilbert–Pollak conjecture](https://en.wikipedia.org/wiki/Gilbert%E2%80%93Pollak_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [GP68] Gilbert, E. N., Pollak, H. O., _Steiner minimal trees_, SIAM J. Appl. Math. 16 (1968),
  1–29.
- [IT12] Ivanov, A. O., Tuzhilin, A. A., _The Steiner ratio Gilbert–Pollak conjecture is still
  open_, Algorithmica 62 (2012), 630–632.
- [IT14] Ivanov, A. O., Tuzhilin, A. A., _Du–Hwang characteristic area: Catch-22_,
  [arXiv:1402.6079](https://arxiv.org/abs/1402.6079).
-/

namespace GilbertPollakConjecture

open scoped EuclideanGeometry Finset

variable {X : Type*} [MetricSpace X]

/-- The total length of a graph `G` whose vertices are points of a metric space: the sum, over the
edges of `G`, of the distance between the two endpoints of the edge. -/
noncomputable def graphLength {V : Type*} [MetricSpace V] [Fintype V] (G : SimpleGraph V) : ℝ :=
  open scoped Classical in
  ∑ e ∈ G.edgeFinset, Sym2.lift ⟨dist, dist_comm⟩ e

/-- The length of a minimum spanning tree of a finite set `S` of points of a metric space:
the least total length of a tree whose vertex set is exactly `S`, where each edge has the
distance between its endpoints as its length.

In the Euclidean plane this is the length of a Euclidean minimum spanning tree of `S`. -/
noncomputable def mstLength (S : Finset X) : ℝ :=
  sInf {graphLength T | (T : SimpleGraph S) (_ : T.IsTree)}

/-- The length of a Steiner minimum tree of a finite set `S` of points of a metric space: the
infimum of the total lengths of trees connecting the points of `S` that may use finitely many
additional vertices (Steiner points), i.e. the infimum of the minimum spanning tree lengths of
the finite supersets of `S`. -/
noncomputable def smtLength (S : Finset X) : ℝ :=
  sInf {mstLength Q | (Q : Finset X) (_ : S ⊆ Q)}

/-- The Steiner ratio of a metric space `X`: the infimum, over all finite sets `S` of at least two
points of `X`, of the ratio of the length of a Steiner minimum tree of `S` to the length of a
minimum spanning tree of `S`.

This is the convention of the Wikipedia list of unsolved problems (a number at most `1`); the
Wikipedia article on the conjecture uses the reciprocal convention (the supremum of the ratio of
the minimum spanning tree length to the Steiner minimum tree length). -/
noncomputable def steinerRatio (X : Type*) [MetricSpace X] : ℝ :=
  sInf {smtLength S / mstLength S | (S : Finset X) (_ : 2 ≤ #S)}

/-- **Gilbert–Pollak conjecture**, stated as in the Wikipedia list of unsolved problems: the
Steiner ratio of the Euclidean plane is $\sqrt{3}/2$, i.e.
$$\inf_{S} \frac{\operatorname{SMT}(S)}{\operatorname{MST}(S)} = \frac{\sqrt{3}}{2},$$
the infimum being over all finite sets $S$ of at least two points in the plane. -/
theorem gilbert_pollak_conjecture.variants.steinerRatio_eq : steinerRatio ℝ² = √3 / 2 := by
  sorry

end GilbertPollakConjecture

theorem GilbertPollakConjecture.gilbert_pollak_conjecture.variants.steinerRatio_eq.disproof : ¬ (type_of% @GilbertPollakConjecture.gilbert_pollak_conjecture.variants.steinerRatio_eq) := sorry
