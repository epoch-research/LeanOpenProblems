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

/-- Every eternal dominating set is a dominating set. -/
@[category API, AMS 5]
theorem IsEternalDominating.isDominating {G : SimpleGraph V} {D : Finset V}
    (hD : IsEternalDominating G D) : G.IsDominating (D : Set V) :=
  let ⟨_, h𝓕, hD⟩ := hD
  h𝓕.1 D hD

/-- In a complete graph with at least one vertex, a single guard suffices: it simply moves to
every attacked vertex. -/
@[category test, AMS 5]
theorem isEternalDominating_singleton_top (v : V) :
    IsEternalDominating (⊤ : SimpleGraph V) {v} := by
  refine ⟨Set.range fun w : V => ({w} : Finset V), ⟨?_, ?_⟩, v, rfl⟩
  · rintro D ⟨w, rfl⟩ u
    by_cases huw : u = w
    · exact Or.inl (by simp [huw])
    · exact Or.inr ⟨w, by simp, huw⟩
  · rintro D ⟨w, rfl⟩ r hr
    have hwr : w ≠ r := fun h => hr (by simp [h])
    exact ⟨w, by simp, hwr, r, by simp⟩

/-- The empty set is not an eternal dominating set of a graph with a vertex. -/
@[category test, AMS 5]
theorem not_isEternalDominating_empty (G : SimpleGraph V) [Nonempty V] :
    ¬ IsEternalDominating G ∅ := by
  rintro ⟨𝓕, h𝓕, h⟩
  obtain ⟨v⟩ := ‹Nonempty V›
  simpa using h𝓕.1 ∅ h v

/-- The centre of the path on three vertices is a dominating set but not an eternal dominating
set: after the guard moves to defend an attack at an end vertex, the other end vertex is no
longer dominated. -/
@[category test, AMS 5]
theorem not_isEternalDominating_pathGraph_three :
    ¬ IsEternalDominating (pathGraph 3) {1} := by
  rintro ⟨𝓕, h𝓕, hD⟩
  obtain ⟨v, hv, -, hmem⟩ := h𝓕.2 _ hD 0 (by decide)
  have hv' : v = 1 := by simpa using hv
  subst hv'
  rw [show insert (0 : Fin 3) (({1} : Finset (Fin 3)).erase 1) = {0} by decide] at hmem
  simpa [pathGraph_adj] using h𝓕.1 {0} hmem 2

/-- The eternal domination number of a nonempty complete graph is `1`. -/
@[category test, AMS 5]
theorem eternalDominationNumber_top [Nonempty V] : γ∞((⊤ : SimpleGraph V)) = 1 := by
  obtain ⟨v⟩ := ‹Nonempty V›
  refine le_antisymm (Nat.sInf_le ⟨{v}, isEternalDominating_singleton_top v, by simp⟩) ?_
  refine le_csInf ⟨1, {v}, isEternalDominating_singleton_top v, by simp⟩ ?_
  rintro n ⟨D, hD, rfl⟩
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
  rintro rfl
  simpa using hD.isDominating v

variable [Fintype V]

/-- The whole vertex set is an eternal dominating set: no vertex is ever unoccupied. -/
@[category API, AMS 5]
theorem isEternalDominating_univ (G : SimpleGraph V) : IsEternalDominating G Finset.univ := by
  refine ⟨{Finset.univ}, ⟨fun D hD v => Or.inl ?_, fun D hD r hr => ?_⟩, rfl⟩
  · rw [Set.mem_singleton_iff.mp hD]
    exact Finset.mem_univ v
  · rw [Set.mem_singleton_iff.mp hD] at hr
    exact (hr (Finset.mem_univ r)).elim

/-- The eternal domination number is at most the number of vertices. -/
@[category API, AMS 5]
theorem eternalDominationNumber_le_card (G : SimpleGraph V) : γ∞(G) ≤ Fintype.card V :=
  Nat.sInf_le ⟨Finset.univ, isEternalDominating_univ G, Finset.card_univ⟩

/-- Every eternal dominating set is a dominating set, so $\gamma(G) \leq \gamma_\infty(G)$. -/
@[category API, AMS 5]
theorem dominationNumber_le_eternalDominationNumber (G : SimpleGraph V) : γ(G) ≤ γ∞(G) := by
  refine csInf_le_csInf' ⟨_, Finset.univ, isEternalDominating_univ G, rfl⟩ ?_
  rintro n ⟨D, hD, rfl⟩
  exact ⟨D, hD.isDominating, rfl⟩

/-- **γ–θ conjecture.** Does there exist a (finite simple) graph $G$ whose domination number
$\gamma(G)$, eternal domination number $\gamma_\infty(G)$ (one-guard-moves model) and clique
covering number $\theta(G)$ satisfy $\gamma(G) = \gamma_\infty(G) < \theta(G)$?

Here $\theta(G)$ is expressed as the chromatic number of the complement of $G$, to which it is
equal. Since $\gamma(G) \leq \gamma_\infty(G) \leq \theta(G)$ for every graph, such a graph exists
if and only if the γ–θ conjecture, "$\gamma(G) = \gamma_\infty(G)$ if and only if
$\gamma(G) = \theta(G)$ for every graph $G$", is false. This is Question 1 of [KM15a]. -/
@[category research open, AMS 5 91]
theorem conjecture :
    answer(sorry) ↔
      ∃ (n : ℕ) (G : SimpleGraph (Fin n)), γ(G) = γ∞(G) ∧ (γ(G) : ℕ∞) < θ(G) := by
  sorry

end Conjecture
