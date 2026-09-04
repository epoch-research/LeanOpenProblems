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
# Cereceda's conjecture

Cereceda's conjecture concerns the diameter of the space of $(d + 2)$-colourings of a
$d$-degenerate graph, where two proper colourings are adjacent when they differ on exactly one
vertex. It states that this diameter is $O(n^2)$ for graphs on $n$ vertices.

*References:*
- [Wikipedia, Cereceda's conjecture](https://en.wikipedia.org/wiki/Cereceda%27s_conjecture)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Graph_theory)
- [BH19] Bousquet, N., Heinrich, M., *A polynomial version of Cereceda's conjecture*,
  [arXiv:1903.05619](https://arxiv.org/abs/1903.05619)
- [EF18] Eiben, E., Feghali, C., *Towards Cereceda's conjecture for planar graphs*,
  [arXiv:1810.00731](https://arxiv.org/abs/1810.00731)
- [Ce07] Cereceda, L., *Mixing graph colourings*, PhD thesis, London School of Economics (2007),
  [http://etheses.lse.ac.uk/131/](http://etheses.lse.ac.uk/131/)
-/

namespace CerecedasConjecture

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/--
A graph `G` is `d`-degenerate if every nonempty subgraph of `G` has a vertex of degree at
most `d`. Equivalently, every nonempty set `S` of vertices contains a vertex with at most `d`
neighbours in `S`. The degeneracy of `G` is the least `d` for which `G` is `d`-degenerate, so
`IsDegenerate G d` says exactly that the degeneracy of `G` is at most `d`.
-/
def IsDegenerate (d : ℕ) : Prop :=
  ∀ S : Set V, S.Nonempty → ∃ v ∈ S, (G.neighborSet v ∩ S).encard ≤ d

/--
The `k`-recolouring graph (also called the `k`-reconfiguration graph) of `G`: its vertices are
the proper `k`-colourings of `G`, and two colourings are adjacent when they differ on exactly
one vertex, i.e. when one is obtained from the other by recolouring a single vertex.
-/
def recoloringGraph (k : ℕ) : SimpleGraph (G.Coloring (Fin k)) where
  Adj α β := ∃ v, α v ≠ β v ∧ ∀ w, w ≠ v → α w = β w
  symm _ _ := fun ⟨v, hv, h⟩ => ⟨v, hv.symm, fun w hw => (h w hw).symm⟩
  loopless _ := fun ⟨_, hv, _⟩ => hv rfl

/--
**Cereceda's conjecture** (Cereceda, 2007; see [BH19], Conjecture 3).

For every $d$ there is a constant $C_d$ such that for every graph $G$ on $n$ vertices with
degeneracy at most $d$ (every nonempty subgraph of $G$ has a vertex of degree at most $d$), the
diameter of the space of proper $(d + 2)$-colourings of $G$ is at most $C_d \cdot n^2$. Here two
colourings are adjacent if they differ on exactly one vertex, so this says that any two proper
$(d + 2)$-colourings of $G$ can be transformed into each other by a sequence of at most
$C_d \cdot n^2$ single-vertex recolourings through proper $(d + 2)$-colourings. In other words,
the diameter of the space of $(d + 2)$-colourings of $d$-degenerate graphs is $O(n^2)$.

Since `SimpleGraph.ediam` takes the value `⊤` on a disconnected graph with at least two
vertices, the bound also asserts that the recolouring graph is connected. The constant $C_d$ is
allowed to depend on $d$, following [BH19], where the version with a constant independent of $d$
is stated separately as a stronger question.
-/
theorem cerecedas_conjecture (d : ℕ) :
    ∃ C : ℕ, ∀ {V : Type} [Fintype V] (G : SimpleGraph V), IsDegenerate G d →
      (recoloringGraph G (d + 2)).ediam ≤ C * Fintype.card V ^ 2 := by
  sorry

end CerecedasConjecture

theorem CerecedasConjecture.cerecedas_conjecture.disproof : ¬ (type_of% @CerecedasConjecture.cerecedas_conjecture) := sorry
