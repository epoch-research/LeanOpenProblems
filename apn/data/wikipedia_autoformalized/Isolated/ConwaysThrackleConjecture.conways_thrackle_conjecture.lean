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
# Conway's thrackle conjecture

A *thrackle* is a drawing of a finite simple graph in the plane in which the vertices are
distinct points, each edge is a Jordan arc (a simple continuous curve) joining the points of its
two endpoints and passing through no other vertex, and every pair of distinct edges meets exactly
once: two edges sharing an endpoint meet only at that common endpoint, and two edges with no
common endpoint meet at exactly one point of their interiors, where they must cross properly
(transversally), i.e. one curve passes from one side of the other curve to its other side.

John H. Conway conjectured that every thrackle has at most as many edges as vertices.

*References:*
- [Wikipedia, Conway's thrackle conjecture](https://en.wikipedia.org/wiki/Conway%27s_thrackle_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [LPS97] Lovász, L., Pach, J., Szegedy, M., _On Conway's thrackle conjecture_.
  Discrete Comput. Geom. 18 (1997), 369–376.
- [FP11] Fulek, R., Pach, J., _A computational approach to Conway's thrackle conjecture_.
  Comput. Geom. 44 (2011), 345–355. [arXiv:1002.3904](https://arxiv.org/abs/1002.3904)
- [FP19] Fulek, R., Pach, J., _Thrackles: An improved upper bound_.
  Discrete Appl. Math. 259 (2019), 226–231. [arXiv:1708.08037](https://arxiv.org/abs/1708.08037)
-/

namespace ConwaysThrackleConjecture

open Topology
open scoped unitInterval EuclideanGeometry

/--
The curve `δ : I → ℝ²` **crosses** the curve `γ : I → ℝ²` at the interior parameter `s₀` if
the point `δ s₀` lies on `γ` and, in some neighbourhood `U` of `δ s₀`, the points of `δ` just
before `s₀` and just after `s₀` lie on different sides of `γ`: they cannot be joined by a path
inside `U` that avoids `γ`. This is the informal condition that `δ` passes from one side of `γ`
to its other side at `δ s₀`, as opposed to touching `γ` tangentially.
-/
def CrossesAt (γ δ : I → ℝ²) (s₀ : I) : Prop :=
  0 < s₀ ∧ s₀ < 1 ∧ δ s₀ ∈ Set.range γ ∧
    ∃ U ∈ 𝓝 (δ s₀), ∀ᶠ s in 𝓝[<] s₀, ∀ᶠ s' in 𝓝[>] s₀,
      ¬ JoinedIn (U \ Set.range γ) (δ s) (δ s')

/--
Two curves `γ δ : I → ℝ²` have a **proper crossing** at the point `p` if `p` is an interior
point of both curves and each curve crosses the other at `p`, i.e. the four half-curves emanating
from `p` alternate around `p`. This is the transversality condition in the definition of a
thrackle.
-/
def IsProperCrossing (γ δ : I → ℝ²) (p : ℝ²) : Prop :=
  ∃ t₀ s₀ : I, γ t₀ = p ∧ δ s₀ = p ∧ CrossesAt γ δ s₀ ∧ CrossesAt δ γ t₀

/--
A **thrackle drawing** of a simple graph `G` in the plane consists of a point `vertex v` for each
vertex `v` and a curve `arc e : I → ℝ²` for each edge `e` such that:
- distinct vertices are drawn as distinct points;
- each edge is drawn as a Jordan arc (a continuous injective curve) whose two endpoints are the
  points representing the two ends of the edge;
- no arc passes through a vertex other than its endpoints;
- every two distinct edges meet in exactly one point (so two edges with a common endpoint
  meet only at that endpoint);
- two edges with no common endpoint cross properly (transversally) at their meeting point.
-/
structure IsThrackleDrawing {V : Type*} (G : SimpleGraph V) (vertex : V → ℝ²)
    (arc : G.edgeSet → I → ℝ²) : Prop where
  vertex_injective : Function.Injective vertex
  continuous : ∀ e, Continuous (arc e)
  arc_injective : ∀ e, Function.Injective (arc e)
  endpoints : ∀ e, s(arc e 0, arc e 1) = (e : Sym2 V).map vertex
  avoids_vertices : ∀ e v, vertex v ∈ Set.range (arc e) → v ∈ (e : Sym2 V)
  meet_once : ∀ e e' : G.edgeSet, e ≠ e' →
    ∃ p, Set.range (arc e) ∩ Set.range (arc e') = {p}
  cross : ∀ e e' : G.edgeSet, (∀ v, v ∈ (e : Sym2 V) → v ∉ (e' : Sym2 V)) →
    ∀ p ∈ Set.range (arc e) ∩ Set.range (arc e'), IsProperCrossing (arc e) (arc e') p

/--
**Conway's thrackle conjecture.** Thrackles cannot have more edges than vertices: if a finite
simple graph $G$ admits a thrackle drawing in the plane, then $|E(G)| \le |V(G)|$.
-/
theorem conways_thrackle_conjecture {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (vertex : V → ℝ²) (arc : G.edgeSet → I → ℝ²)
    (h : IsThrackleDrawing G vertex arc) :
    G.edgeFinset.card ≤ Fintype.card V := by
  sorry

/-- The straight segment on the coordinate axis `i` from `-1` to `1`, parametrised by `I`. -/
noncomputable def axisSegment (i : Fin 2) (t : I) : ℝ² :=
  (2 * (t : ℝ) - 1) • EuclideanSpace.single i 1

/-- The "V"-shaped curve `s ↦ (2s - 1, |2s - 1|)`. It touches the horizontal axis at the origin
from above without crossing it. -/
noncomputable def touchingCurve (s : I) : ℝ² :=
  (2 * (s : ℝ) - 1) • EuclideanSpace.single 0 1 +
    |2 * (s : ℝ) - 1| • EuclideanSpace.single 1 1

end ConwaysThrackleConjecture

theorem ConwaysThrackleConjecture.conways_thrackle_conjecture.disproof : ¬ (type_of% @ConwaysThrackleConjecture.conways_thrackle_conjecture) := sorry
