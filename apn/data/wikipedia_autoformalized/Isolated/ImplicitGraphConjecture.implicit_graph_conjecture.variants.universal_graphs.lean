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
# The implicit graph conjecture

The implicit graph conjecture (Kannan–Naor–Rudich question, Spinrad's conjecture) asserts that
every hereditary family of graphs of at most factorial speed of growth admits an efficient
implicit representation, i.e. an adjacency labeling scheme with $O(\log n)$-bit labels.
It was refuted by Hatami and Hatami (FOCS 2022), who constructed, for every $\delta > 0$,
a hereditary family of at most factorial speed whose implicit representations need labels of
length $\Omega(n^{1/2 - \delta})$. Wikipedia's list of unsolved problems still
records the conjecture as open.

*References:*
- [Wikipedia, Implicit graph](https://en.wikipedia.org/wiki/implicit_graph_conjecture)
- [Wikipedia, List of unsolved problems in mathematics]
  (https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [KNR92] S. Kannan, M. Naor, S. Rudich, *Implicit representation of graphs*,
  SIAM J. Discrete Math. 5 (1992), 596–603.
- [Sp03] J. P. Spinrad, *Efficient Graph Representations*, Fields Institute Monographs 19,
  AMS (2003).
- [HaHa22] H. Hatami, P. Hatami, *The Implicit Graph Conjecture is False*, FOCS 2022,
  [arXiv:2111.13198](https://arxiv.org/abs/2111.13198).
-/

namespace ImplicitGraphConjecture

open SimpleGraph

/-- A family of finite labelled graphs: `F n` is the set of members of the family whose vertex
set is `Fin n`, i.e. the $n$-vertex graphs of the family, following [HaHa22]. -/
abbrev GraphFamily : Type := ∀ n : ℕ, Set (SimpleGraph (Fin n))

/-- A graph family is *hereditary* if it is closed under taking induced subgraphs: whenever
`G ∈ F n` and `H` is a graph on `Fin m` isomorphic to an induced subgraph of `G`, then
`H ∈ F m`. Taking `m = n` shows that a hereditary family is closed under isomorphism.
Equivalently, the family is defined by a (possibly infinite) set of forbidden induced
subgraphs. -/
def IsHereditary (F : GraphFamily) : Prop :=
  ∀ ⦃m n : ℕ⦄, ∀ G ∈ F n, ∀ H : SimpleGraph (Fin m), H ⊴ G → H ∈ F m

/-- A graph family has *at most factorial speed of growth* if the number of $n$-vertex members
is at most $2^{O(n \log n)}$, i.e. there is a constant $C$ with $|F_n| \le 2^{C n \log n}$
for all $n$. -/
def HasAtMostFactorialSpeed (F : GraphFamily) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, ((F n).ncard : ℝ) ≤ 2 ^ (C * n * Real.log n)

/-- A graph family has an *efficient implicit representation* (an *adjacency labeling scheme*
with $O(\log n)$-bit labels) if there are a constant $C$ and a *decoder*
`D : {0,1}* × {0,1}* → Bool`, both depending only on the family, such that every $n$-vertex
member `G` of the family admits a labeling of its vertices by binary strings of length at most
$C \log n$ from which adjacency is recovered by the decoder: `G.Adj u v ↔ D (ℓ u) (ℓ v)`.

Following [HaHa22], no computability or running time requirement is imposed on the decoder. -/
def HasEfficientImplicitRepresentation (F : GraphFamily) : Prop :=
  ∃ (C : ℝ) (D : List Bool → List Bool → Bool), ∀ n : ℕ, ∀ G ∈ F n,
    ∃ ℓ : Fin n → List Bool,
      (∀ v, ((ℓ v).length : ℝ) ≤ C * Real.log n) ∧
        ∀ u v, G.Adj u v ↔ D (ℓ u) (ℓ v) = true

/-- A graph family has *induced-universal graphs of polynomial size* if there is a constant $C$
such that for every $n$ there is a graph $U_n$ on $n^C$ vertices containing every $n$-vertex
member of the family as an induced subgraph. -/
def HasPolynomialUniversalGraphs (F : GraphFamily) : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, ∃ U : SimpleGraph (Fin (n ^ C)), ∀ G ∈ F n, G ⊴ U

/--
**The implicit graph conjecture**, formulated with induced-universal graphs.

Is it true that every hereditary graph family with at most factorial speed of growth has
induced-universal graphs of polynomial size $n^{O(1)}$?

A family has an efficient implicit representation if and only if it has induced-universal graphs
of polynomial size [KNR92], so this is equivalent to `implicit_graph_conjecture` and its answer
is also **no** [HaHa22].
-/
theorem implicit_graph_conjecture.variants.universal_graphs :
    ∀ F : GraphFamily, IsHereditary F → HasAtMostFactorialSpeed F →
      HasPolynomialUniversalGraphs F := by
  sorry

end ImplicitGraphConjecture

theorem ImplicitGraphConjecture.implicit_graph_conjecture.variants.universal_graphs.disproof : ¬ (type_of% @ImplicitGraphConjecture.implicit_graph_conjecture.variants.universal_graphs) := sorry
