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
# Cereceda's conjecture

Cereceda's conjecture concerns the diameter of the space of $(d + 2)$-colourings of a
$d$-degenerate graph, where two proper colourings are adjacent when they differ on exactly one
vertex. It states that this diameter is $O(n^2)$ for graphs on $n$ vertices.

*References:*
- [Wikipedia, Cereceda's conjecture](https://en.wikipedia.org/wiki/Cereceda%27s_conjecture)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Graph_theory)
- [BH19] Bousquet, N., Heinrich, M., *A polynomial version of Cereceda's conjecture*,
  [arXiv:1903.05619](https://arxiv.org/abs/1903.05619)
- [EF18] Eiben, E., Feghali, C., *Towards Cereceda's conjecture for planar graphs*,
  [arXiv:1810.00731](https://arxiv.org/abs/1810.00731)
- [Ce07] Cereceda, L., *Mixing graph colourings*, PhD thesis, London School of Economics (2007),
  [http://etheses.lse.ac.uk/131/](http://etheses.lse.ac.uk/131/)
-/

namespace CerecedasConjecture

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/--
A graph `G` is `d`-degenerate if every nonempty subgraph of `G` has a vertex of degree at
most `d`. Equivalently, every nonempty set `S` of vertices contains a vertex with at most `d`
neighbours in `S`. The degeneracy of `G` is the least `d` for which `G` is `d`-degenerate, so
`IsDegenerate G d` says exactly that the degeneracy of `G` is at most `d`.
-/
def IsDegenerate (d : ℕ) : Prop :=
  ∀ S : Set V, S.Nonempty → ∃ v ∈ S, (G.neighborSet v ∩ S).encard ≤ d

/--
The `k`-recolouring graph (also called the `k`-reconfiguration graph) of `G`: its vertices are
the proper `k`-colourings of `G`, and two colourings are adjacent when they differ on exactly
one vertex, i.e. when one is obtained from the other by recolouring a single vertex.
-/
def recoloringGraph (k : ℕ) : SimpleGraph (G.Coloring (Fin k)) where
  Adj α β := ∃ v, α v ≠ β v ∧ ∀ w, w ≠ v → α w = β w
  symm _ _ := fun ⟨v, hv, h⟩ => ⟨v, hv.symm, fun w hw => (h w hw).symm⟩
  loopless _ := fun ⟨_, hv, _⟩ => hv rfl

@[category API, AMS 5]
theorem recoloringGraph_adj (k : ℕ) (α β : G.Coloring (Fin k)) :
    (recoloringGraph G k).Adj α β ↔ ∃ v, α v ≠ β v ∧ ∀ w, w ≠ v → α w = β w :=
  Iff.rfl

/-- On a one-vertex graph, any two distinct colourings are adjacent in the recolouring graph. -/
@[category test, AMS 5]
theorem recoloringGraph_bot_fin_one (k : ℕ) :
    recoloringGraph (⊥ : SimpleGraph (Fin 1)) k = ⊤ := by
  ext α β
  simp only [recoloringGraph_adj, top_adj]
  refine ⟨fun ⟨_, hv, _⟩ h => hv (h ▸ rfl), fun h => ⟨0, fun h0 => h ?_, ?_⟩⟩
  · exact RelHom.ext fun w => Subsingleton.elim w 0 ▸ h0
  · exact fun w hw => absurd (Subsingleton.elim w 0) hw

@[category API, AMS 5]
theorem IsDegenerate.mono {d d' : ℕ} (h : d ≤ d') (hG : IsDegenerate G d) : IsDegenerate G d' :=
  fun S hS => (hG S hS).imp fun v ⟨hv, hd⟩ => ⟨hv, hd.trans (by exact_mod_cast h)⟩

/-- The edgeless graph is `0`-degenerate. -/
@[category test, AMS 5]
theorem isDegenerate_bot : IsDegenerate (⊥ : SimpleGraph V) 0 := by
  refine fun S hS => hS.imp fun v hv => ⟨hv, ?_⟩
  have : (⊥ : SimpleGraph V).neighborSet v = ∅ := by ext; simp
  simp [this]

/-- The complete graph on `d + 1` vertices is `d`-degenerate. -/
@[category test, AMS 5]
theorem isDegenerate_top_fin (d : ℕ) : IsDegenerate (⊤ : SimpleGraph (Fin (d + 1))) d := by
  intro S hS
  obtain ⟨v, hv⟩ := hS
  refine ⟨v, hv, ?_⟩
  have h1 : (⊤ : SimpleGraph (Fin (d + 1))).neighborSet v ∩ S ⊆ Set.univ \ {v} := by
    intro w hw
    simp only [Set.mem_inter_iff, mem_neighborSet, top_adj] at hw
    exact ⟨Set.mem_univ _, fun h => hw.1 (Set.mem_singleton_iff.mp h).symm⟩
  calc _ ≤ (Set.univ \ {v} : Set (Fin (d + 1))).encard := Set.encard_le_encard h1
    _ = d := by
        rw [Set.encard_diff_singleton_of_mem (Set.mem_univ v), Set.encard_univ,
          ENat.card_eq_coe_fintype_card, Fintype.card_fin]
        norm_cast

/-- The complete graph on `n + 2` vertices is not `n`-degenerate. -/
@[category test, AMS 5]
theorem not_isDegenerate_top (n : ℕ) : ¬ IsDegenerate (⊤ : SimpleGraph (Fin (n + 2))) n := by
  intro h
  obtain ⟨v, -, hv⟩ := h Set.univ Set.univ_nonempty
  have : (⊤ : SimpleGraph (Fin (n + 2))).neighborSet v = Set.univ \ {v} := by ext; simp [eq_comm]
  rw [Set.inter_univ, this, Set.encard_diff_singleton_of_mem (Set.mem_univ v), Set.encard_univ,
    ENat.card_eq_coe_fintype_card, Fintype.card_fin] at hv
  norm_num at hv

/--
**Cereceda's conjecture** (Cereceda, 2007; see [BH19], Conjecture 3).

For every $d$ there is a constant $C_d$ such that for every graph $G$ on $n$ vertices with
degeneracy at most $d$ (every nonempty subgraph of $G$ has a vertex of degree at most $d$), the
diameter of the space of proper $(d + 2)$-colourings of $G$ is at most $C_d \cdot n^2$. Here two
colourings are adjacent if they differ on exactly one vertex, so this says that any two proper
$(d + 2)$-colourings of $G$ can be transformed into each other by a sequence of at most
$C_d \cdot n^2$ single-vertex recolourings through proper $(d + 2)$-colourings. In other words,
the diameter of the space of $(d + 2)$-colourings of $d$-degenerate graphs is $O(n^2)$.

Since `SimpleGraph.ediam` takes the value `⊤` on a disconnected graph with at least two
vertices, the bound also asserts that the recolouring graph is connected. The constant $C_d$ is
allowed to depend on $d$, following [BH19], where the version with a constant independent of $d$
is stated separately as a stronger question.
-/
@[category research open, AMS 5]
theorem cerecedas_conjecture (d : ℕ) :
    ∃ C : ℕ, ∀ {V : Type} [Fintype V] (G : SimpleGraph V), IsDegenerate G d →
      (recoloringGraph G (d + 2)).ediam ≤ C * Fintype.card V ^ 2 := by
  sorry

end CerecedasConjecture
