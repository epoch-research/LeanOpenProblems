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
# Oberwolfach problem

*References:*
- [Wikipedia, Oberwolfach problem](https://en.wikipedia.org/wiki/Oberwolfach_problem)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [GJKKO21] Glock, S., Joos, F., Kim, J., Kühn, D., Osthus, D., *Resolution of the Oberwolfach
  problem*, J. Eur. Math. Soc. 23 (2021), 2511–2547.
  [arXiv:1806.04644](https://arxiv.org/abs/1806.04644)
- [ABHMS16] Alspach, B., Bryant, D., Horsley, D., Maenhaut, B., Scharaschkin, V., *On
  factorisations of complete graphs into circulant graphs and the Oberwolfach problem*,
  Ars Math. Contemp. 11 (2016), 157–173. [arXiv:1411.6047](https://arxiv.org/abs/1411.6047)
- [SDTBD21] Salassa, F., Dragotto, G., Traetta, T., Buratti, M., Della Croce, F., *Merging
  combinatorial design and optimization: the Oberwolfach problem*, Australas. J. Combin. 79 (2021),
  141–166. [arXiv:1903.12112](https://arxiv.org/abs/1903.12112)

The Oberwolfach problem, posed by Ringel in 1967, asks which $2$-regular graphs $G$ have the
property that the complete graph $K_n$ on the same number $n$ of vertices can be decomposed into
edge-disjoint copies of $G$. Every $2$-regular graph is a disjoint union of cycles
$C_x + C_y + C_z + \cdots$ (each of length at least $3$), and the instance for this graph is
denoted $OP(x, y, z, \dots)$. A solution can only exist when $n$ is odd, and then it consists of
exactly $(n-1)/2$ copies of $G$.

It is known that $OP(4, 5)$ and $OP(3, 3, 5)$ have no solution. It is widely believed that every
other instance has a solution; this is known for all sufficiently large $n$ [GJKKO21] and for all
$n \le 60$ [SDTBD21].

The problem has also been extended to even $n$: there one asks whether all edges of $K_n$ except
those of a perfect matching can be decomposed into copies of $G$ (necessarily $n/2 - 1$ of them).
Here $OP(3, 3)$ and $OP(3, 3, 3, 3)$ have no solution, and it is widely believed that every other
even instance has one.
-/

namespace OberwolfachProblem

open SimpleGraph

variable {V : Type*}

/--
A graph `H` on a vertex set `V` *decomposes into copies of* a graph `G` on the same vertex set
if there is a set `D` of graphs on `V`, each isomorphic to `G`, whose edge sets are pairwise
disjoint and whose union is `H`. Equivalently, every edge of `H` lies in exactly one member of `D`.
-/
def DecomposesIntoCopiesOf (H G : SimpleGraph V) : Prop :=
  ∃ D : Set (SimpleGraph V),
    (∀ C ∈ D, Nonempty (C ≃g G)) ∧ D.PairwiseDisjoint edgeSet ∧ sSup D = H

/--
**The Oberwolfach problem for even orders.** Let $G$ be a $2$-regular graph on an even number $n$
of vertices. Then there is a perfect matching $I$ of the complete graph $K_n$ on the same vertex
set such that $K_n - I$ (all edges of $K_n$ except those of $I$) can be decomposed into
edge-disjoint copies of $G$ (necessarily $n/2 - 1$ of them) if and only if $G$ is not one of the
two known exceptions $C_3 + C_3$ (the instance $OP(3, 3)$, $n = 6$) and $C_3 + C_3 + C_3 + C_3$
(the instance $OP(3, 3, 3, 3)$, $n = 12$), which are known to have no solution.

Since every perfect matching of $K_n$ is mapped to every other one by an automorphism of $K_n$,
the existential quantifier over $I$ may equivalently be read as a universal one.
-/
theorem oberwolfach_problem.variants.even [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsRegularOfDegree 2) (hV : Even (Fintype.card V)) :
    (∃ I : (⊤ : SimpleGraph V).Subgraph, I.IsPerfectMatching ∧
      DecomposesIntoCopiesOf (⊤ \ I.spanningCoe) G) ↔
      IsEmpty (G ≃g cycleGraph 3 ⊕g cycleGraph 3) ∧
      IsEmpty (G ≃g cycleGraph 3 ⊕g cycleGraph 3 ⊕g cycleGraph 3 ⊕g cycleGraph 3) := by
  sorry

end OberwolfachProblem

theorem OberwolfachProblem.oberwolfach_problem.variants.even.disproof : ¬ (type_of% @OberwolfachProblem.oberwolfach_problem.variants.even) := sorry
