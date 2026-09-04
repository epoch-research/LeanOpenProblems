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
# Overfull conjecture

The *overfull conjecture* of Chetwynd and Hilton (1986): a finite simple graph $G$ on $n$
vertices with maximum degree $\Delta(G) > n/3$ is class 2 if and only if it has an overfull
subgraph $S$ with $\Delta(S) = \Delta(G)$.

A finite graph $H$ is *overfull* if $|E(H)| > \Delta(H) \lfloor |V(H)|/2 \rfloor$. A graph $G$ is
*class 2* if its chromatic index $\chi'(G)$ (the least number of colours in a proper edge
colouring) equals $\Delta(G) + 1$. By Vizing's theorem, $\chi'(G)$ is always $\Delta(G)$ or
$\Delta(G) + 1$.

The Wikipedia list entry writes the hypothesis as $\Delta(G) \geq n/3$. We follow the original
paper and the Wikipedia article on overfull graphs, which use the strict bound $\Delta(G) > n/3$.
The bound cannot be relaxed: the Petersen graph with one vertex deleted ($n = 9$, $\Delta = 3$)
is class 2 but has no overfull subgraph $S$ with $\Delta(S) = 3$.

*References:*
- [Wikipedia, Overfull graph](https://en.wikipedia.org/wiki/Overfull_graph%23Overfull_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- A. G. Chetwynd, A. J. W. Hilton, *Star multigraphs with three vertices of maximum degree*,
  Math. Proc. Cambridge Philos. Soc. 100 (1986), 303–317.
  [doi:10.1017/S030500410006610X](https://doi.org/10.1017/S030500410006610X)
-/

namespace OverfullConjecture

open SimpleGraph

/-- The *chromatic index* $\chi'(G)$ of `G`: the least number of colours in a proper edge
colouring of `G`, i.e. the chromatic number of the line graph of `G`. -/
noncomputable def chromaticIndex {V : Type*} (G : SimpleGraph V) : ℕ∞ :=
  G.lineGraph.chromaticNumber

variable {V : Type*} [Fintype V]

/-- A finite simple graph `G` is *overfull* if $|E(G)| > \Delta(G) \lfloor |V(G)| / 2 \rfloor$.
Here `Fintype.card V / 2` is natural-number division, i.e. the floor of $|V(G)| / 2$. -/
def IsOverfull [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.maxDegree * (Fintype.card V / 2) < G.edgeFinset.card

/-- A finite simple graph `G` is *class 2* if its chromatic index is $\Delta(G) + 1$. -/
def IsClassTwo (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  chromaticIndex G = G.maxDegree + 1

open scoped Classical in
/-- **Overfull conjecture** (Chetwynd–Hilton, 1986).

A finite simple graph $G$ on $n$ vertices with maximum degree $\Delta(G) > n/3$ is class 2
(that is, its chromatic index is $\Delta(G) + 1$) if and only if it has an overfull subgraph
$S$ (that is, $|E(S)| > \Delta(S) \lfloor |V(S)|/2 \rfloor$) satisfying
$\Delta(S) = \Delta(G)$.

The subgraph $S$ is not required to be induced or spanning. The "if" direction is a known
elementary fact; the "only if" direction is the open part of the conjecture. -/
theorem overfull_conjecture (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : (Fintype.card V : ℝ) / 3 < G.maxDegree) :
    IsClassTwo G ↔
      ∃ S : G.Subgraph, IsOverfull S.coe ∧ S.coe.maxDegree = G.maxDegree := by
  sorry

end OverfullConjecture

theorem OverfullConjecture.overfull_conjecture.disproof : ¬ (type_of% @OverfullConjecture.overfull_conjecture) := sorry
