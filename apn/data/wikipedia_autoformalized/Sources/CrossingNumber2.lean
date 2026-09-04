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
# Guy's conjecture on the crossing number of complete graphs

A *drawing* of a graph in the plane maps the vertices to distinct points and every edge to a
simple arc (an arbitrary curve, not necessarily a straight line segment) joining the images of
its endpoints, so that no vertex lies on an edge that it is not an endpoint of, and any two edges
meet in finitely many points outside their endpoints. A *crossing* is such a common point, counted
once for every pair of edges passing through it. The crossing number $\mathrm{cr}(G)$ of $G$ is
the minimum number of crossings over all drawings of $G$.

Guy (1960) exhibited drawings of the complete graph $K_n$ showing that
$$\mathrm{cr}(K_n) \le Z(n) := \frac14 \left\lfloor \frac{n}{2} \right\rfloor
\left\lfloor \frac{n-1}{2} \right\rfloor \left\lfloor \frac{n-2}{2} \right\rfloor
\left\lfloor \frac{n-3}{2} \right\rfloor,$$
and conjectured that no drawing of any complete graph does better, i.e. $\mathrm{cr}(K_n) = Z(n)$
for all $n$. This is known for $n \le 12$ (Saaty, Pan–Richter) and open in general.

*References:*
- [Wikipedia, Crossing number (graph theory)](https://en.wikipedia.org/wiki/crossing_number_%28graph_theory%29)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Gu60] Guy, R. K., *A combinatorial problem*, Nabla (Bull. Malayan Math. Soc.) 7 (1960), 68–72.
- [PaRi07] Pan, S. and Richter, R. B., *The crossing number of $K_{11}$ is 100*,
  J. Graph Theory 56 (2007), 128–134.
-/

open scoped EuclideanGeometry unitInterval

namespace CrossingNumber2

variable {V : Type*} (G : SimpleGraph V)

/-- A (topological) drawing of the simple graph `G` in the plane. Vertices are mapped to distinct
points, and every edge is mapped to a simple arc (an injective continuous curve) whose two
endpoints are the images of the endpoints of the edge. The interior of an arc passes through no
vertex, and any two distinct arcs have only finitely many common interior points. Edges are
allowed to be arbitrary curves, not just straight line segments.

The arcs are not required to cross transversally at their common interior points: every common
interior point of two arcs is counted as a crossing. Since a touching point can be removed by a
local redrawing without creating new crossings, this does not change the minimum number of
crossings. -/
structure Drawing where
  /-- The position of each vertex in the plane. -/
  vertex : V → ℝ²
  vertex_injective : Function.Injective vertex
  /-- The curve representing each edge, parametrised by the unit interval. -/
  arc : G.edgeSet → C(I, ℝ²)
  arc_injective (e : G.edgeSet) : Function.Injective (arc e)
  arc_endpoints (e : G.edgeSet) : s(arc e 0, arc e 1) = Sym2.map vertex e
  arc_avoids_vertex (e : G.edgeSet) (t : I) (ht : t ∈ Set.Ioo 0 1) (v : V) : arc e t ≠ vertex v
  finite_inter (e f : G.edgeSet) (hef : e ≠ f) :
    (arc e '' Set.Ioo 0 1 ∩ arc f '' Set.Ioo 0 1).Finite

variable {G}

/-- The number of crossings of a drawing: the number of pairs `(p, {e, f})` where `e ≠ f` are
edges and `p` is a common point of the arcs of `e` and `f` other than a shared endpoint
(equivalently, a common interior point of the two arcs). A point through which several edges pass
is thus counted once for every pair of edges through it. The count is finite whenever `G` has
finitely many edges. -/
noncomputable def Drawing.crossings (D : Drawing G) : ℕ∞ :=
  {x : ℝ² × Sym2 G.edgeSet | ∃ e f, e ≠ f ∧ x.2 = s(e, f) ∧
    x.1 ∈ D.arc e '' Set.Ioo 0 1 ∩ D.arc f '' Set.Ioo 0 1}.encard

/-- Guy's upper bound
$Z(n) = \frac14 \lfloor n/2 \rfloor \lfloor (n-1)/2 \rfloor \lfloor (n-2)/2 \rfloor
\lfloor (n-3)/2 \rfloor$
on the crossing number of the complete graph $K_n$. The product is always divisible by `4`, so the
natural number division is exact. -/
def guyBound (n : ℕ) : ℕ :=
  n / 2 * ((n - 1) / 2) * ((n - 2) / 2) * ((n - 3) / 2) / 4

/-- Guy's bound takes the values $1, 3, 9, 18, 36, 60, 100, 150, 225, 315$ for $n = 5, \dots, 14$
(OEIS A000241). -/
@[category test, AMS 5]
theorem guyBound_values :
    (List.range 10).map (fun i => guyBound (i + 5)) =
      [1, 3, 9, 18, 36, 60, 100, 150, 225, 315] := by
  decide

/-- Guy's bound vanishes for $n \le 4$, where $K_n$ is planar. -/
@[category test, AMS 5]
theorem guyBound_eq_zero (n : ℕ) (hn : n ≤ 4) : guyBound n = 0 := by
  interval_cases n <;> rfl

/-- **Guy's conjecture on the crossing number of complete graphs.**
Is there a drawing of some complete graph $K_n$ with fewer than
$Z(n) = \frac14 \lfloor n/2 \rfloor \lfloor (n-1)/2 \rfloor \lfloor (n-2)/2 \rfloor
\lfloor (n-3)/2 \rfloor$ crossings, the number given by Guy's upper bound? Guy conjectured that
the answer is no, i.e. that $\mathrm{cr}(K_n) = Z(n)$ for every $n$. -/
@[category research open, AMS 5]
theorem crossing_number_2 :
    answer(sorry) ↔
      ∃ n, ∃ D : Drawing (SimpleGraph.completeGraph (Fin n)), D.crossings < guyBound n := by
  sorry

end CrossingNumber2
