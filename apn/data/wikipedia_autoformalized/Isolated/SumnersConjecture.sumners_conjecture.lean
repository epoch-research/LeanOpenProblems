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
# Sumner's conjecture

Sumner's universal tournament conjecture (1971) states that every orientation of every
$n$-vertex tree is a subgraph of every $(2n-2)$-vertex tournament. Kühn, Mycroft and Osthus
proved it for all sufficiently large $n$; it remains open in general.

We use `Digraph.IsTournament` and `Digraph.IsOrientation` from
`FormalConjecturesForMathlib.Combinatorics.Digraph.Tournament`.

*References:*
* [Wikipedia: Sumner's conjecture](https://en.wikipedia.org/wiki/Sumner%27s_conjecture)
* [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [KMO11a] Kühn, D., Mycroft, R., Osthus, D. (2011). "An approximate version of Sumner's
  universal tournament conjecture." *J. Combin. Theory Ser. B* 101, pp. 415--447.
  [arXiv:1010.4429](https://arxiv.org/abs/1010.4429)
* [KMO11b] Kühn, D., Mycroft, R., Osthus, D. (2011). "A proof of Sumner's universal tournament
  conjecture for large tournaments." *Proc. Lond. Math. Soc.* 102, pp. 731--766.
  [arXiv:1010.4430](https://arxiv.org/abs/1010.4430)
-/

namespace SumnersConjecture

/--
**Sumner's conjecture.**

Does every $(2n-2)$-vertex tournament contain as a subgraph every $n$-vertex oriented tree?

That is, for every $n \geq 2$, every tournament $G$ on exactly $2n - 2$ vertices, every tree
$T$ on exactly $n$ vertices and every orientation $D$ of $T$, is there an injective map from the
vertices of $D$ to the vertices of $G$ that sends every arc of $D$ to an arc of $G$? The copy of
$D$ in $G$ need not be induced.

The restriction $n \geq 2$ excludes the degenerate case $n = 1$, where the tournament on
$2n - 2 = 0$ vertices cannot contain the one-vertex tree.
-/
theorem sumners_conjecture : 
    ∀ n : ℕ, 2 ≤ n →
      ∀ {W : Type*} [Fintype W] (G : Digraph W), G.IsTournament → Fintype.card W = 2 * n - 2 →
      ∀ {V : Type*} [Fintype V] (T : SimpleGraph V) (D : Digraph V),
        T.IsTree → D.IsOrientation T → Fintype.card V = n →
        ∃ f : V → W, Function.Injective f ∧ ∀ u v, D.Adj u v → G.Adj (f u) (f v) := by
  sorry

end SumnersConjecture

theorem SumnersConjecture.sumners_conjecture.disproof : ¬ (type_of% @SumnersConjecture.sumners_conjecture) := sorry
