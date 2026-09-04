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
# Henson graph

For $i \geq 3$, the Henson graph $G_i$ is the unique countable homogeneous graph that contains
no $i$-vertex clique but contains every finite $K_i$-free graph as an induced subgraph. Here a
graph is *homogeneous* if every isomorphism between finite induced subgraphs extends to an
automorphism of the whole graph. The first of these graphs, $G_3$, is also called the homogeneous
triangle-free graph or the universal triangle-free graph.

Wikipedia's list of unsolved problems asks: *do the Henson graphs have the finite model
property?* That is, does every first-order sentence in the language of graphs that holds in $G_i$
also hold in some finite graph? In other words, is $G_i$ pseudofinite? The case $i = 3$ is a
well-known question of Cherlin about the generic triangle-free graph.

*References:*
- [Wikipedia, Henson graph](https://en.wikipedia.org/wiki/Henson_graph)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [He71] C. Ward Henson, *A family of countable homogeneous graphs*,
  Pacific Journal of Mathematics 38 (1971), 69–83.
- [Ch11] G. Cherlin, *Two problems on homogeneous structures, revisited*, in: Model Theoretic
  Methods in Finite Combinatorics, Contemporary Mathematics 558, AMS (2011), 319–415.
-/

namespace HensonGraph

open FirstOrder Language SimpleGraph

variable {V : Type}

/-- A simple graph `G` on the vertex type `V` is a *Henson graph* $G_i$ if `V` is countable, `G`
contains no clique on `i` vertices, `G` contains every finite $K_i$-free graph as an induced
subgraph, and `G` is homogeneous, i.e. every isomorphism between finite induced subgraphs of `G`
extends to an automorphism of `G`.

Homogeneity is expressed via `FirstOrder.Language.IsUltrahomogeneous` for the structure
`G.structure` in the language of graphs: since this language is relational, its finitely generated
substructures are exactly the finite induced subgraphs, and its embeddings are exactly the
induced-subgraph embeddings.

For every `i ≥ 3` such a graph exists and is unique up to isomorphism; see [He71]. -/
structure IsHensonGraph (i : ℕ) (G : SimpleGraph V) : Prop where
  countable : Countable V
  cliqueFree : G.CliqueFree i
  universal : ∀ (W : Type) [Finite W] (H : SimpleGraph W), H.CliqueFree i → Nonempty (H ↪g G)
  isUltrahomogeneous : letI := G.structure; Language.graph.IsUltrahomogeneous V

/-- A simple graph `G` has the *finite model property* (equivalently, `G` is *pseudofinite*) if
every first-order sentence in the language of graphs that holds in `G` also holds in some finite
simple graph. This says exactly that the complete first-order theory of `G` has the finite model
property. -/
def HasFiniteModelProperty (G : SimpleGraph V) : Prop :=
  ∀ φ : Language.graph.Sentence, (letI := G.structure; V ⊨ φ) →
    ∃ (W : Type) (H : SimpleGraph W), Finite W ∧ (letI := H.structure; W ⊨ φ)

/-- Do the Henson graphs have the finite model property? That is, for every $i \geq 3$, does every
first-order sentence in the language of graphs that holds in the Henson graph $G_i$ also hold in
some finite graph? Since $G_i$ is unique up to isomorphism, the question is stated for every
graph satisfying the defining properties of $G_i$. -/
theorem henson_graph :
    ∀ i ≥ 3, ∀ (V : Type) (G : SimpleGraph V), IsHensonGraph i G →
      HasFiniteModelProperty G := by
  sorry

end HensonGraph

theorem HensonGraph.henson_graph.disproof : ¬ (type_of% @HensonGraph.henson_graph) := sorry
