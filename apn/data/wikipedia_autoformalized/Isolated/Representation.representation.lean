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
# Graphs with high representation number

A graph $G = (V, E)$ is *word-representable* if there is a word $w$ over the alphabet $V$,
containing every letter of $V$, such that two distinct letters $x, y$ alternate in $w$ if and
only if $xy \in E$. Letters $x$ and $y$ alternate in $w$ if deleting all other letters from $w$
leaves a word of the form $xyxy\ldots$ or $yxyx\ldots$.

The graph $G$ is *$k$-representable* if it is represented by a $k$-uniform word, that is, a word
with exactly $k$ copies of each letter. A graph is word-representable if and only if it is
$k$-representable for some $k$, and $k$-representability implies $(k+1)$-representability.
The *representation number* of $G$ is the least such $k$; it is $\infty$ for graphs that are not
word-representable.

Every non-complete word-representable graph on $n$ vertices with clique number $\kappa(G)$ is
$2(n - \kappa(G))$-representable. The highest known representation number of a graph on $n$
vertices is $\lfloor n/2 \rfloor$, attained by a crown graph with an additional all-adjacent
vertex. Whether a graph on $n$ vertices can require more than $\lfloor n/2 \rfloor$ copies of each
letter is open.

*References:*
- [Wikipedia, Word-representable graph](https://en.wikipedia.org/wiki/Word-representable_graph)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [S. Kitaev, *A comprehensive introduction to the theory of word-representable
  graphs*](https://arxiv.org/abs/1705.05924)
- M. Halldórsson, S. Kitaev, A. Pyatkin, *Semi-transitive orientations and word-representable
  graphs*, Discrete Appl. Math. 201 (2016), 164–171.
- M. E. Glen, S. Kitaev, A. Pyatkin, *On the representation number of a crown graph*,
  Discrete Appl. Math. 244 (2018), 89–93.
-/

namespace Representation

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- Letters `a` and `b` *alternate* in the word `w` if, after deleting from `w` all letters other
than `a` and `b`, no two consecutive letters are equal. For `a ≠ b` this says the remaining word
is of the form `abab...` or `baba...`. -/
def Alternate (w : List V) (a b : V) : Prop :=
  (w.filter fun x => x = a ∨ x = b).IsChain (· ≠ ·)

/-- A word `w` over the alphabet `V` *represents* the graph `G` if every letter of `V` occurs in
`w` and two distinct letters alternate in `w` if and only if they are adjacent in `G`. -/
def Represents (w : List V) (G : SimpleGraph V) : Prop :=
  (∀ v, v ∈ w) ∧ ∀ a b, a ≠ b → (G.Adj a b ↔ Alternate w a b)

/-- A graph is *word-representable* if some word represents it. -/
def WordRepresentable (G : SimpleGraph V) : Prop :=
  ∃ w : List V, Represents w G

/-- A graph is *`k`-representable* if it is represented by a `k`-uniform word, that is, a word
containing exactly `k` copies of each letter. -/
def IsKRepresentable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ w : List V, (∀ v, w.count v = k) ∧ Represents w G

/-- The *representation number* of a graph `G` is the least `k` such that `G` is
`k`-representable. It is `⊤` if `G` is not word-representable. -/
noncomputable def representationNumber (G : SimpleGraph V) : ℕ∞ :=
  ⨅ k ∈ setOf (IsKRepresentable G), (k : ℕ∞)

/--
Are there any graphs on $n$ vertices whose representation requires more than
$\lfloor n/2 \rfloor$ copies of each letter?

That is, is there a word-representable graph $G$ on $n$ vertices whose representation number
exceeds $\lfloor n/2 \rfloor$? The restriction to word-representable graphs is implicit, since a
graph that is not word-representable has representation number $\infty$.

The restriction $n \geq 4$ excludes the degenerate cases $n \leq 3$. There
$\lfloor n/2 \rfloor \leq 1$, while the one-vertex graph has representation number $1$ and every
non-complete word-representable graph (for example the path on three vertices) has
representation number at least $2$. Every graph on at most five vertices is a circle graph and so
has representation number at most $2$; hence any threshold from $4$ to $6$ gives the same
statement.

The highest known representation number is $\lfloor n/2 \rfloor$, attained by a crown graph with
an additional all-adjacent vertex.
-/
theorem representation :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      4 ≤ n ∧ WordRepresentable G ∧ (n / 2 : ℕ) < representationNumber G := by
  sorry

end Representation

theorem Representation.representation.disproof : ¬ (type_of% @Representation.representation) := sorry
