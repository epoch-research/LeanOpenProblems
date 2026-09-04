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
# Gyárfás–Sumner conjecture

The Gyárfás–Sumner conjecture on $\chi$-boundedness of graphs with a forbidden induced tree.

*References:*
- [Wikipedia: Gyárfás–Sumner conjecture](https://en.wikipedia.org/wiki/Gy%C3%A1rf%C3%A1s%E2%80%93Sumner_conjecture)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Gy75] A. Gyárfás, *On Ramsey covering-numbers*, Infinite and finite sets (Colloq., Keszthely,
  1973), Vol. II, North-Holland, 1975.
- [Su81] D. P. Sumner, *Subtrees of a graph and the chromatic number*, The theory and applications
  of graphs (Kalamazoo, Mich., 1980), Wiley, 1981.
-/

namespace GyarfasSumnerConjecture

open SimpleGraph

/--
**Gyárfás–Sumner conjecture.** For any fixed pair of a tree $T$ and a complete graph $K_t$, the
graphs that are both $T$-free and $K_t$-free are $\chi$-bounded. That is, for every finite tree
$T$ and every $t$, there is a constant $c$ (depending only on $T$ and $t$) such that every finite
graph $G$ containing neither $T$ nor $K_t$ as an induced subgraph satisfies $\chi(G) \le c$.

Here `T ⊴ G` means that `G` has an induced subgraph isomorphic to `T` (there is a graph embedding
`T ↪g G`), and `G.CliqueFree t` means that `G` has no clique on `t` vertices, i.e. no induced
subgraph isomorphic to $K_t$. A tree is a connected acyclic graph, so `T` is nonempty.
-/
@[category research open, AMS 5]
theorem gyarfas_sumner_conjecture {α : Type*} [Fintype α] (T : SimpleGraph α) (hT : T.IsTree)
    (t : ℕ) :
    ∃ c : ℕ, ∀ {β : Type*} [Fintype β] (G : SimpleGraph β),
      ¬ T ⊴ G → G.CliqueFree t → G.chromaticNumber ≤ c := by
  sorry

end GyarfasSumnerConjecture
