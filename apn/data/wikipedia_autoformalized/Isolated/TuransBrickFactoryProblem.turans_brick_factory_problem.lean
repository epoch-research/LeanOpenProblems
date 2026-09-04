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
# Turán's brick factory problem

Turán's brick factory problem asks for the minimum number of crossings in a drawing of the
complete bipartite graph $K_{m,n}$ in the plane. A drawing places the vertices at distinct points,
draws each edge as a curve joining its two endpoints, and puts no vertex on the curve of an edge
that it is not incident to. A crossing is a common point of the curves of two distinct edges that
is not a vertex. This is the standard definition of the crossing number, as in de Klerk et al.
(pairwise intersections of edges at a point other than a vertex).

Zarankiewicz (and independently Urbanik) showed that $K_{m,n}$ can always be drawn with
$$Z(m,n) = \left\lfloor \frac{m}{2} \right\rfloor \left\lfloor \frac{m-1}{2} \right\rfloor
\left\lfloor \frac{n}{2} \right\rfloor \left\lfloor \frac{n-1}{2} \right\rfloor$$
crossings. The question is whether some complete bipartite graph can be drawn with fewer
crossings. The conjectured answer is no, that is $\operatorname{cr}(K_{m,n}) = Z(m,n)$ for all
$m, n$. This is the *Zarankiewicz crossing number conjecture*. It is known for
$\min(m, n) \le 6$ and for $K_{7,7}$, $K_{7,8}$, $K_{7,9}$, but open in general.

*References:*
- [Wikipedia, Turán's brick factory problem](https://en.wikipedia.org/wiki/Tur%C3%A1n%27s_brick_factory_problem)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- E. de Klerk, J. Maharry, D. V. Pasechnik, R. B. Richter, G. Salazar,
  [Improved bounds for the crossing numbers of $K_{m,n}$ and $K_n$](https://arxiv.org/abs/math/0404142)
-/

open scoped EuclideanGeometry

namespace TuransBrickFactoryProblem

variable {V : Type*}

/-- A *drawing* of a simple graph `G` in the plane: distinct vertices are drawn as distinct
points, each edge `uv` is drawn as a continuous curve from the point of `u` to the point of `v`
(the curve of `vu` being the reverse of the curve of `uv`), and no vertex lies on the curve of an
edge that it is not incident to. -/
structure Drawing (G : SimpleGraph V) where
  /-- The point of the plane at which the vertex `v` is drawn. -/
  vertex : V → ℝ²
  /-- Distinct vertices are drawn as distinct points. -/
  vertex_injective : Function.Injective vertex
  /-- The curve drawn for the edge `uv`. -/
  curve : ∀ ⦃u v : V⦄, G.Adj u v → Path (vertex u) (vertex v)
  /-- The curve drawn for `vu` is the reverse of the curve drawn for `uv`, so that each edge
  has a single well-defined curve. -/
  curve_symm : ∀ ⦃u v : V⦄ (h : G.Adj u v), curve h.symm = (curve h).symm
  /-- A vertex lying on the curve of an edge is an endpoint of that edge. -/
  eq_or_eq_of_vertex_mem_curve : ∀ ⦃u v : V⦄ (h : G.Adj u v) ⦃w : V⦄,
    vertex w ∈ Set.range (curve h) → w = u ∨ w = v

namespace Drawing

variable {G : SimpleGraph V} (D : Drawing G)

/-- `D.OnEdge p e` means that the point `p` lies on the curve that `D` draws for the edge `e`. -/
def OnEdge (p : ℝ²) (e : Sym2 V) : Prop :=
  ∃ (u v : V) (h : G.Adj u v), e = s(u, v) ∧ p ∈ Set.range (D.curve h)

/-- The crossings of the drawing `D`: an unordered pair of two *distinct* edges together with a
point of the plane that lies on the curves of both edges and is not a vertex. A point where `k`
edges meet therefore contributes `k.choose 2` crossings. -/
def crossingSet : Set (Sym2 (Sym2 V) × ℝ²) :=
  {x | ¬ x.1.IsDiag ∧ x.2 ∉ Set.range D.vertex ∧ ∀ e ∈ x.1, D.OnEdge x.2 e}

/-- The number of crossings of the drawing `D`, as an element of `ℕ∞` (it is `⊤` when the
drawing has infinitely many crossings). -/
noncomputable def crossings : ℕ∞ :=
  D.crossingSet.encard

end Drawing

/-- The Zarankiewicz number
$Z(m,n) = \lfloor m/2 \rfloor \lfloor (m-1)/2 \rfloor \lfloor n/2 \rfloor \lfloor (n-1)/2 \rfloor$,
the number of crossings of Zarankiewicz's drawing of $K_{m,n}$. -/
def zarankiewicz (m n : ℕ) : ℕ :=
  (m / 2) * ((m - 1) / 2) * (n / 2) * ((n - 1) / 2)

/-- **Turán's brick factory problem.**
Is there a drawing of some complete bipartite graph $K_{m,n}$ in the plane with fewer crossings
than the number $Z(m,n)$ given by Zarankiewicz? The conjectured answer is no: this is the
Zarankiewicz crossing number conjecture $\operatorname{cr}(K_{m,n}) = Z(m,n)$. -/
theorem turans_brick_factory_problem :
    ∃ (m n : ℕ) (D : Drawing (completeBipartiteGraph (Fin m) (Fin n))),
      D.crossings < zarankiewicz m n := by
  sorry

end TuransBrickFactoryProblem

theorem TuransBrickFactoryProblem.turans_brick_factory_problem.disproof : ¬ (type_of% @TuransBrickFactoryProblem.turans_brick_factory_problem) := sorry
