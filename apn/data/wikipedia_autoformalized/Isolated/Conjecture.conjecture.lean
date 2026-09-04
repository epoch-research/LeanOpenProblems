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
# The γ–θ conjecture (eternal domination)

The *eternal domination game* (one-guard-moves model) is played on a finite graph $G$ by a
defender and an attacker. The defender first places guards on a dominating set $D_1$ (at most one
guard per vertex). Then, at each turn, the attacker attacks a vertex $r_i$. If $r_i$ is unoccupied,
the defender must move exactly one guard from a vertex of $D_i$ adjacent to $r_i$ onto $r_i$; the
new configuration $D_{i+1}$ must again be a dominating set. The defender wins if they can defend
every infinite sequence of attacks. A set $D$ is an *eternal dominating set* if the defender wins
when starting from $D$, and the *eternal domination number* $\gamma_\infty(G)$ is the minimum size
of an eternal dominating set. This is the model of Burger et al.; it is not the *m-eternal*
(all-guards-move) variant.

The *clique covering number* $\theta(G)$ is the minimum number of cliques partitioning the
vertices of $G$; equivalently, it is the chromatic number of the complement of $G$.

Since $\gamma(G) \leq \gamma_\infty(G) \leq \theta(G)$, where $\gamma$ is the domination number,
the γ–θ conjecture ($\gamma(G) = \gamma_\infty(G)$ if and only if $\gamma(G) = \theta(G)$, for
every graph $G$) fails exactly when there is a graph $G$ with
$\gamma(G) = \gamma_\infty(G) < \theta(G)$. Whether such a graph exists is Question 1 of
Klostermeyer and Mynhardt [KM15a], listed as one of the main open questions in the survey
[KM15b]. Such a graph must contain a triangle and have maximum degree at least four [KM15a].

*References:*
- [Wikipedia, *Eternal dominating set*, § Open questions](https://en.wikipedia.org/wiki/Eternal_dominating_set%23Open_questions)
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [KM15a] W. F. Klostermeyer and C. M. Mynhardt, *Domination, Eternal Domination, and Clique
  Covering*, Discuss. Math. Graph Theory 35 (2015), 283–300.
  [arXiv:1407.5235](https://arxiv.org/abs/1407.5235)
- [KM15b] W. F. Klostermeyer and C. M. Mynhardt, *Protecting a graph with mobile guards*,
  Appl. Anal. Discrete Math. 10 (2016), 1–29. [arXiv:1407.5228](https://arxiv.org/abs/1407.5228)
-/

namespace Conjecture

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- A family `𝓕` of vertex sets of `G` is an *eternal dominating family* (one-guard-moves model)
if every member of `𝓕` is a dominating set and, for every configuration `D ∈ 𝓕` and every
attack at an unoccupied vertex `r ∉ D`, some guard standing on a vertex `v ∈ D` adjacent to `r`
can move to `r` so that the new configuration `(D \ {v}) ∪ {r}` again lies in `𝓕`.

Attacks at occupied vertices need no response, so they are not modelled. -/
def IsEternalDominatingFamily (G : SimpleGraph V) (𝓕 : Set (Finset V)) : Prop :=
  (∀ D ∈ 𝓕, G.IsDominating (D : Set V)) ∧
    ∀ D ∈ 𝓕, ∀ r ∉ D, ∃ v ∈ D, G.Adj v r ∧ insert r (D.erase v) ∈ 𝓕

/-- A finite set `D` of vertices of `G` is an *eternal dominating set* if placing one guard on
each vertex of `D` lets the defender defend every infinite sequence of attacks, moving one guard
per attack and keeping the guards on a dominating set. Equivalently, `D` belongs to some eternal
dominating family: the defender wins by always staying inside that family (the eternal domination
game is a safety game, so positional strategies suffice). -/
def IsEternalDominating (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∃ 𝓕, IsEternalDominatingFamily G 𝓕 ∧ D ∈ 𝓕

/-- The *eternal domination number* $\gamma_\infty(G)$ of `G` is the least size of an eternal
dominating set of `G` (in the one-guard-moves model). For a finite graph this is a true minimum,
since the whole vertex set is an eternal dominating set. -/
noncomputable def eternalDominationNumber (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ D : Finset V, IsEternalDominating G D ∧ D.card = n}

/-- The domination number $\gamma(G)$. -/
local notation "γ(" G ")" => dominationNumber G

/-- The eternal domination number $\gamma_\infty(G)$ (one-guard-moves model). -/
local notation "γ∞(" G ")" => eternalDominationNumber G

/-- The clique covering number $\theta(G)$: the least number of cliques partitioning the vertex
set of `G`, which is the chromatic number of the complement of `G`. -/
local notation "θ(" G ")" => chromaticNumber Gᶜ

variable [Fintype V]

/-- **γ–θ conjecture.** Does there exist a (finite simple) graph $G$ whose domination number
$\gamma(G)$, eternal domination number $\gamma_\infty(G)$ (one-guard-moves model) and clique
covering number $\theta(G)$ satisfy $\gamma(G) = \gamma_\infty(G) < \theta(G)$?

Here $\theta(G)$ is expressed as the chromatic number of the complement of $G$, to which it is
equal. Since $\gamma(G) \leq \gamma_\infty(G) \leq \theta(G)$ for every graph, such a graph exists
if and only if the γ–θ conjecture, "$\gamma(G) = \gamma_\infty(G)$ if and only if
$\gamma(G) = \theta(G)$ for every graph $G$", is false. This is Question 1 of [KM15a]. -/
theorem conjecture :
    
      ∃ (n : ℕ) (G : SimpleGraph (Fin n)), γ(G) = γ∞(G) ∧ (γ(G) : ℕ∞) < θ(G) := by
  sorry

end Conjecture

theorem Conjecture.conjecture.disproof : ¬ (type_of% @Conjecture.conjecture) := sorry
