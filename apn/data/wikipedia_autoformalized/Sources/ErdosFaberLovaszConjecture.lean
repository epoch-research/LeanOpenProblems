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
# Erdős–Faber–Lovász conjecture

The Erdős–Faber–Lovász conjecture (1972) is a problem about coloring unions of cliques. It says:
if $k$ complete graphs, each having exactly $k$ vertices, have the property that every pair of
complete graphs has at most one shared vertex, then the union of the graphs can be properly
colored with $k$ colors.

Kang, Kelly, Kühn, Methuku and Osthus proved the conjecture for all sufficiently large $k$.
The conjecture for every $k$ remains open.

*References:*
- [Wikipedia, Erdős–Faber–Lovász conjecture](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Faber%E2%80%93Lov%C3%A1sz_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- D. Y. Kang, T. Kelly, D. Kühn, A. Methuku, D. Osthus,
  *A proof of the Erdős–Faber–Lovász conjecture*, Ann. of Math. (2) 198 (2023), 537–618.
  [arXiv:2101.04698](https://arxiv.org/abs/2101.04698)
-/

namespace ErdosFaberLovaszConjecture

open SimpleGraph

/--
Two vertices are adjacent in the union of the complete graphs on the vertex sets `C i` if and
only if they are distinct and both lie in some `C i`.
-/
@[category API, AMS 5]
lemma iSup_spanningCoe_completeGraph_adj {V : Type*} {k : ℕ} (C : Fin k → Finset V) (u v : V) :
    (⨆ i, (completeGraph (C i : Set V)).spanningCoe).Adj u v ↔
      u ≠ v ∧ ∃ i, u ∈ C i ∧ v ∈ C i := by
  simp only [iSup_adj, spanningCoe, map_adj, completeGraph, top_adj, ne_eq,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨i, ⟨a, ha⟩, ⟨b, hb⟩, hab, rfl, rfl⟩
    exact ⟨fun h => hab (Subtype.ext h), i, by simpa using ha, by simpa using hb⟩
  · rintro ⟨hne, i, hu, hv⟩
    exact ⟨i, ⟨u, by simpa using hu⟩, ⟨v, by simpa using hv⟩,
      fun h => hne (congrArg Subtype.val h), rfl, rfl⟩

/--
**Erdős–Faber–Lovász conjecture.**
If $k$ complete graphs, each having exactly $k$ vertices, have the property that every pair of
complete graphs has at most one shared vertex, then the union of the graphs can be properly
colored with $k$ colors.

Here the $i$-th complete graph has vertex set `C i`, so its edges are all pairs of distinct
vertices of `C i`, and the union of the graphs is `⨆ i, (completeGraph (C i : Set V)).spanningCoe`.
The vertex set of this union is the union of the `C i`, so the hypothesis `hcover` says that the
vertex type `V` is exactly this vertex set. The conclusion `Colorable k` says that this graph has
a proper coloring with $k$ colors.
-/
@[category research open, AMS 5]
theorem erdos_faber_lovasz_conjecture {V : Type*} [DecidableEq V] (k : ℕ) (C : Fin k → Finset V)
    (hcard : ∀ i, (C i).card = k)
    (hinter : Pairwise fun i j => (C i ∩ C j).card ≤ 1)
    (hcover : ∀ v, ∃ i, v ∈ C i) :
    (⨆ i, (completeGraph (C i : Set V)).spanningCoe).Colorable k := by
  sorry

end ErdosFaberLovaszConjecture
