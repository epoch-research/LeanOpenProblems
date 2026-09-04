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
# Unfriendly partition conjecture

An *unfriendly partition* (or *majority colouring*) of a graph is a partition of its vertex set
into disjoint subsets such that every vertex has at least as many neighbours in the other subsets
as in its own subset. Every finite graph has an unfriendly partition into two parts (a maximum cut
is one). Shelah and Milner showed that an uncountable graph need not have an unfriendly partition
into two parts, although every graph has one into three parts. The case of countable graphs is
open.

*References:*
- [Wikipedia: Unfriendly partition](https://en.wikipedia.org/wiki/unfriendly_partition)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- R. Aharoni, E. C. Milner, K. Prikry, *Unfriendly partitions of a graph*,
  J. Combin. Theory Ser. B 50 (1990), 1--10.
- S. Shelah, E. C. Milner, *Graphs with no unfriendly partitions*, in *A tribute to Paul Erdős*,
  Cambridge University Press (1990), 373--384.
-/

namespace UnfriendlyPartitionConjecture

/--
**Unfriendly partition conjecture.** Does every countable graph have an unfriendly partition
into two parts?

That is, for every simple graph $G$ on a countable (finite or countably infinite) vertex set, is
there a $2$-colouring `c` of the vertices such that every vertex $v$ has at least as many
neighbours of the other colour as neighbours of its own colour? The two sets of neighbours are
compared as cardinals, so the condition is meaningful for vertices of infinite degree.
-/
@[category research open, AMS 5]
theorem unfriendly_partition_conjecture :
    answer(sorry) ↔ ∀ (V : Type*) [Countable V] (G : SimpleGraph V),
      ∃ c : V → Fin 2, ∀ v : V,
        Cardinal.mk {w : V // G.Adj v w ∧ c w = c v} ≤
          Cardinal.mk {w : V // G.Adj v w ∧ c w ≠ c v} := by
  sorry

end UnfriendlyPartitionConjecture
