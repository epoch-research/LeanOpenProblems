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
# Bipartite graphs: do crown graphs require the longest word-representants?

A graph $G = (V, E)$ is *word-representable* if there is a word $w$ over the alphabet $V$ (every
letter of $V$ occurring in $w$) such that two distinct letters $x, y$ *alternate* in $w$ if and
only if $xy \in E$. Here $x$ and $y$ alternate in $w$ if deleting from $w$ all letters other than
$x$ and $y$ leaves a word of the form $xyxy\cdots$ or $yxyx\cdots$ (of even or odd length). The
graph $G$ is *$k$-representable* if it is represented by a word containing exactly $k$ copies of
each letter; the least such $k$ is the *representation number* $\mathcal{R}(G)$. A word
representing a graph on $n$ vertices with $k$ copies of each letter has length $kn$, so
$\mathcal{R}(G)$ measures the length of the shortest uniform word-representant of $G$. Every
bipartite graph is word-representable.

The *crown graph* $H_{m,m}$ is obtained from the complete bipartite graph $K_{m,m}$ by removing a
perfect matching. Glen, Kitaev and Pyatkin proved that $\mathcal{R}(H_{m,m}) = \lceil m/2 \rceil$
for $m \ge 5$.

The open problem asks whether, among all bipartite graphs, the crown graphs require the longest
word-representants: is $\mathcal{R}(G) \le \mathcal{R}(H_{m,m})$ for every bipartite graph $G$
on $2m$ vertices?

*References:*
- [Wikipedia, Bipartite graph](https://en.wikipedia.org/wiki/bipartite_graph)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- S. Kitaev, *A comprehensive introduction to the theory of word-representable graphs*,
  [arXiv:1705.05924](https://arxiv.org/abs/1705.05924)
- M. Glen, S. Kitaev, A. Pyatkin, *On the representation number of a crown graph*,
  Discrete Applied Mathematics 244 (2018), 89–93,
  [arXiv:1609.00674](https://arxiv.org/abs/1609.00674)
- S. Kitaev, V. Lozin, *Words and Graphs*, Monographs in Theoretical Computer Science,
  Springer (2015)
-/

namespace BipartiteGraph

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- Two letters `x` and `y` *alternate* in the word `w` if deleting from `w` all letters other
than `x` and `y` leaves a word with no two consecutive equal letters, i.e. a word of the form
`xyxy…` or `yxyx…` (of even or odd length). -/
def Alternate (w : List V) (x y : V) : Prop :=
  (w.filter fun z => z = x ∨ z = y).IsChain (· ≠ ·)

/-- A word `w` over the alphabet `V` *represents* the graph `G` if every letter of `V` occurs in
`w`, and two distinct letters alternate in `w` if and only if they are adjacent in `G`. -/
def IsRepresentedBy (G : SimpleGraph V) (w : List V) : Prop :=
  (∀ v, v ∈ w) ∧ ∀ x y, x ≠ y → (Alternate w x y ↔ G.Adj x y)

/-- The graph `G` is *`k`-representable* if it is represented by a word containing exactly `k`
copies of each letter. -/
def IsKRepresentable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ w : List V, IsRepresentedBy G w ∧ ∀ v, w.count v = k

/-- The *representation number* $\mathcal{R}(G)$ of `G`: the least `k` such that `G` is
`k`-representable. By the `sInf` convention it is `0` when `G` is not word-representable; this
does not occur for bipartite graphs, which are all word-representable. -/
noncomputable def representationNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | IsKRepresentable G k}

/-- The *crown graph* on the vertex type `α ⊕ α`: the complete bipartite graph
`completeBipartiteGraph α α` with the perfect matching `{Sum.inl i, Sum.inr i}` removed. For
`α = Fin m` this is the crown graph $H_{m,m}$ on $2m$ vertices. -/
def crownGraph (α : Type*) : SimpleGraph (α ⊕ α) :=
  completeBipartiteGraph α α \ fromRel fun a b => ∃ i, a = Sum.inl i ∧ b = Sum.inr i

/--
**Glen–Kitaev–Pyatkin (2018).** For $m \ge 5$ the crown graph $H_{m,m}$ has representation
number $\lceil m/2 \rceil$. (The restriction $m \ge 5$ is needed: $H_{4,4}$ is the $3$-cube,
whose representation number is $3$.)
-/
theorem representationNumber_crownGraph (m : ℕ) (hm : 5 ≤ m) :
    representationNumber (crownGraph (Fin m)) = (m + 1) / 2 := by
  sorry

end BipartiteGraph

theorem BipartiteGraph.representationNumber_crownGraph.disproof : ¬ (type_of% @BipartiteGraph.representationNumber_crownGraph) := sorry
