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
# Line graphs of non-word-representable graphs

Two distinct letters $x$ and $y$ *alternate* in a word $w$ if, after deleting from $w$ all
letters other than $x$ and $y$, one obtains a word of the form $xyxy\dots$ or $yxyx\dots$
(of even or odd length).

A finite simple graph $G = (V, E)$ is *word-representable* if there is a word $w$ over the
alphabet $V$, in which every letter of $V$ occurs at least once, such that two distinct letters
$x, y \in V$ alternate in $w$ if and only if $xy \in E$.

The *line graph* $L(G)$ of $G$ has the edges of $G$ as vertices, two of them being adjacent when
the corresponding edges of $G$ share an endpoint (Mathlib's `SimpleGraph.lineGraph`).

Kitaev, Salimov, Severs and Úlfarsson showed that many line graphs are not word-representable
(for instance $L(K_n)$ for $n \ge 5$, and $L^k(G)$ for $k \ge 4$ whenever $G$ is connected and
is neither a path, nor a cycle, nor the claw $K_{1,3}$). The following question is open:
is the line graph of a non-word-representable graph always non-word-representable?

*References:*
- [Wikipedia: Line graph](https://en.wikipedia.org/wiki/line_graph)
- [Wikipedia: Word-representable graph](https://en.wikipedia.org/wiki/Word-representable_graph)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- S. Kitaev, *A comprehensive introduction to the theory of word-representable graphs*,
  [arXiv:1705.05924](https://arxiv.org/abs/1705.05924).
- S. Kitaev, P. Salimov, C. Severs, H. Úlfarsson, *On the representability of line graphs*,
  Developments in Language Theory (DLT 2011), LNCS 6795, 478--479.
- S. Kitaev, V. Lozin, *Words and Graphs*, Springer, 2015.
-/

namespace LineGraph

open scoped Classical in
/-- Two letters `x` and `y` *alternate* in the word `w` if, after deleting from `w` all letters
other than `x` and `y`, no two consecutive letters of the resulting word are equal, i.e. the
resulting word is of the form `xyxy…` or `yxyx…`. -/
def Alternate {V : Type*} (w : List V) (x y : V) : Prop :=
  (w.filter fun z => z = x ∨ z = y).IsChain (· ≠ ·)

/-- A simple graph `G` on the vertex type `V` is *word-representable* if there is a (finite) word
`w` over the alphabet `V`, in which every vertex occurs at least once, such that two distinct
vertices `x` and `y` alternate in `w` if and only if they are adjacent in `G`. -/
def WordRepresentable {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ w : List V, (∀ v, v ∈ w) ∧ ∀ x y, x ≠ y → (G.Adj x y ↔ Alternate w x y)

/--
Is the line graph of a non-word-representable graph always non-word-representable?

That is, is it true that for every finite simple graph $G$, if $G$ is not word-representable,
then its line graph $L(G)$ is not word-representable either?
-/
theorem line_graph :
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      ¬ WordRepresentable G → ¬ WordRepresentable G.lineGraph := by
  sorry

end LineGraph

theorem LineGraph.line_graph.disproof : ¬ (type_of% @LineGraph.line_graph) := sorry
