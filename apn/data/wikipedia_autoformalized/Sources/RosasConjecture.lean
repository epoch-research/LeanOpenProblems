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
# Rosa's conjecture

Rosa's conjecture states that all triangular cacti are graceful or nearly-graceful.

A *triangular cactus* is a connected graph all of whose blocks are triangles. Equivalently,
it is a connected graph in which every edge lies on a cycle and every cycle has length three.

A *graceful labeling* of a graph with $m$ edges is an injective labeling of the vertices by
integers in $\{0, \dots, m\}$ such that the absolute differences of the labels of the endpoints
of the edges are exactly $\{1, \dots, m\}$. A *near-graceful labeling* of a graph with $m$ edges
is an injective labeling of the vertices by integers in $\{0, \dots, m + 1\}$ such that the
absolute differences of the labels of the endpoints of the edges are pairwise distinct (these
differences then lie in $\{1, \dots, m + 1\}$).

Rosa's original form of the conjecture is sharper: a triangular cactus with $t$ triangles is
graceful when $t \equiv 0, 1 \pmod 4$ and nearly-graceful when $t \equiv 2, 3 \pmod 4$. In the
latter case it has $m = 3t \equiv 1, 2 \pmod 4$ edges and is Eulerian, so it cannot be graceful
by Rosa's parity theorem.

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Graceful labeling](https://en.wikipedia.org/wiki/Graceful_labeling)
- [Wikipedia, Cactus graph](https://en.wikipedia.org/wiki/Cactus_graph)
- A. Rosa, *Cyclic Steiner triple systems and labelings of triangular cacti*,
  Scientia, Ser. A, Math. Sci. 1 (1988), 87–95.
- J. A. Gallian, *A dynamic survey of graph labeling*,
  [Electron. J. Combin., DS6](https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS6).
-/

namespace RosasConjecture

open SimpleGraph

variable {V : Type*}

/-- The label that a vertex labeling `f` induces on an edge `e`: the absolute difference
$|f(u) - f(v)|$ of the labels of its endpoints. -/
def edgeLabel (f : V → ℕ) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun u v => ((f u : ℤ) - f v).natAbs, fun u v => by
    show ((f u : ℤ) - f v).natAbs = ((f v : ℤ) - f u).natAbs
    rw [← Int.natAbs_neg, neg_sub]⟩

@[simp, category API, AMS 5]
lemma edgeLabel_mk (f : V → ℕ) (u v : V) : edgeLabel f s(u, v) = ((f u : ℤ) - f v).natAbs :=
  rfl

/-- A *triangular cactus* is a connected graph all of whose blocks are triangles. Equivalently,
it is a connected graph in which every edge lies on a cycle (i.e. no edge is a bridge) and
every cycle has length three.

This includes the one-vertex graph (no edges, no cycles), which is trivially graceful. -/
def IsTriangularCactus (G : SimpleGraph V) : Prop :=
  G.Connected ∧ (∀ e ∈ G.edgeSet, ¬ G.IsBridge e) ∧
    ∀ (v : V) (p : G.Walk v v), p.IsCycle → p.length = 3

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A *graceful labeling* of a graph `G` with `m` edges is an injective map
`f : V → {0, …, m}` whose induced edge labels are exactly `{1, …, m}`. -/
def IsGracefulLabeling (f : V → ℕ) : Prop :=
  Function.Injective f ∧ (∀ v, f v ≤ G.edgeFinset.card) ∧
    G.edgeFinset.image (edgeLabel f) = Finset.Icc 1 G.edgeFinset.card

/-- A graph is *graceful* if it admits a graceful labeling. -/
def IsGraceful : Prop :=
  ∃ f : V → ℕ, IsGracefulLabeling G f

/-- A *near-graceful labeling* of a graph `G` with `m` edges is an injective map
`f : V → {0, …, m + 1}` whose induced edge labels are pairwise distinct. Since the vertex
labels are distinct and lie in `{0, …, m + 1}`, the edge labels automatically lie in
`{1, …, m + 1}`. -/
def IsNearGracefulLabeling (f : V → ℕ) : Prop :=
  Function.Injective f ∧ (∀ v, f v ≤ G.edgeFinset.card + 1) ∧
    Set.InjOn (edgeLabel f) G.edgeSet

/-- A graph is *near-graceful* if it admits a near-graceful labeling. -/
def IsNearGraceful : Prop :=
  ∃ f : V → ℕ, IsNearGracefulLabeling G f

variable {G}

@[category API, AMS 5]
lemma IsGracefulLabeling.isNearGracefulLabeling {f : V → ℕ} (hf : IsGracefulLabeling G f) :
    IsNearGracefulLabeling G f := by
  obtain ⟨hinj, hle, himage⟩ := hf
  refine ⟨hinj, fun v => (hle v).trans (Nat.le_succ _), ?_⟩
  rw [← coe_edgeFinset, ← Finset.card_image_iff, himage]
  simp

/-- Every graceful graph is near-graceful. -/
@[category API, AMS 5]
lemma IsGraceful.isNearGraceful (h : IsGraceful G) : IsNearGraceful G :=
  h.imp fun _ hf => hf.isNearGracefulLabeling

/-- The one-vertex graph is a (degenerate) triangular cactus with no triangles. -/
@[category test, AMS 5]
lemma isTriangularCactus_bot_unit : IsTriangularCactus (⊥ : SimpleGraph Unit) := by
  refine ⟨connected_bot_iff.mpr ⟨inferInstance, inferInstance⟩, by simp, fun v p hp => ?_⟩
  cases p with
  | nil => exact absurd rfl hp.ne_nil
  | cons h _ => exact absurd h (by simp)

/-- The one-vertex graph is graceful. -/
@[category test, AMS 5]
lemma isGraceful_bot_unit : IsGraceful (⊥ : SimpleGraph Unit) :=
  ⟨fun _ => 0, fun _ _ _ => rfl, fun _ => Nat.zero_le _, by simp⟩

/-- The triangle is a triangular cactus. -/
@[category test, AMS 5]
lemma isTriangularCactus_top_fin_three : IsTriangularCactus (⊤ : SimpleGraph (Fin 3)) := by
  refine ⟨connected_top, fun e _ => ?_, fun v p hp => ?_⟩
  · induction e using Sym2.ind with | _ u v
    rw [isBridge_iff_adj_and_forall_cycle_notMem]
    rintro ⟨huv, hcyc⟩
    have huv' := huv.ne
    obtain ⟨w, hwu, hwv⟩ : ∃ w : Fin 3, w ≠ u ∧ w ≠ v := by
      clear hcyc huv; revert u v; decide
    refine hcyc (Walk.cons huv (Walk.cons ((top_adj v w).mpr hwv.symm)
      (Walk.cons ((top_adj w u).mpr hwu) Walk.nil))) ?_ (by simp)
    rw [Walk.cons_isCycle_iff]
    constructor
    · simp [Walk.isPath_def, hwu, hwv.symm, huv'.symm]
    · simp [huv', huv'.symm, hwu.symm, hwv.symm]
  · refine le_antisymm ?_ hp.three_le_length
    have := hp.support_nodup.length_le_card
    simpa [Walk.length_support] using this

/-- The triangle is graceful, with labels `0`, `1`, `3`. -/
@[category test, AMS 5]
lemma isGraceful_top_fin_three : IsGraceful (⊤ : SimpleGraph (Fin 3)) :=
  ⟨![0, 1, 3], by unfold IsGracefulLabeling; decide⟩

/-- A single edge is not a triangular cactus: the edge is a bridge. -/
@[category test, AMS 5]
lemma not_isTriangularCactus_top_fin_two : ¬ IsTriangularCactus (⊤ : SimpleGraph (Fin 2)) := by
  rintro ⟨-, hb, -⟩
  refine hb s(0, 1) (by simp) (isBridge_iff_mem_and_forall_cycle_notMem.mpr ⟨by simp, ?_⟩)
  intro u p hp _
  have h1 := hp.three_le_length
  have h2 := hp.support_nodup.length_le_card
  simp [Walk.length_support] at h2
  omega

/-- The butterfly graph: two triangles `{0, 1, 2}` and `{0, 3, 4}` sharing the vertex `0`.
It is the triangular cactus with `t = 2` triangles and `m = 6` edges. -/
def butterfly : SimpleGraph (Fin 5) :=
  fromEdgeSet {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(0, 4), s(3, 4)}

instance : DecidableRel butterfly.Adj := by
  unfold butterfly; infer_instance

/-- The butterfly graph is near-graceful: the labels `0, 7, 5, 4, 3` induce the pairwise
distinct edge labels `7, 5, 2, 4, 3, 1`. (It is not graceful, since it is Eulerian with
`6 ≡ 2 (mod 4)` edges.) -/
@[category test, AMS 5]
lemma isNearGraceful_butterfly : IsNearGraceful butterfly := by
  refine ⟨![0, 7, 5, 4, 3], by decide, by decide, ?_⟩
  rw [← coe_edgeFinset, ← Finset.card_image_iff]
  decide

/--
**Rosa's conjecture.** Every triangular cactus is graceful or near-graceful.

Here a triangular cactus is a finite connected graph all of whose blocks are triangles.
A graph with $m$ edges is graceful if there is an injective vertex labeling
$f : V \to \{0, \dots, m\}$ whose induced edge labels $|f(u) - f(v)|$ are exactly
$\{1, \dots, m\}$, and near-graceful if there is an injective vertex labeling
$f : V \to \{0, \dots, m + 1\}$ whose induced edge labels are pairwise distinct
(and hence lie in $\{1, \dots, m + 1\}$).

Since every graceful graph is near-graceful (`IsGraceful.isNearGraceful`), the conclusion is
equivalent to `IsNearGraceful G`.
-/
@[category research open, AMS 5]
theorem rosas_conjecture (hG : IsTriangularCactus G) : IsGraceful G ∨ IsNearGraceful G := by
  sorry

/--
The graceful half of Rosa's original (1988) formulation of the conjecture: a triangular cactus
with $t \equiv 0, 1 \pmod 4$ triangles is graceful. Here $t$ is the number of $3$-cliques of $G$,
which are exactly its blocks.

For $t \equiv 2, 3 \pmod 4$ a triangular cactus is Eulerian with $3t \equiv 1, 2 \pmod 4$ edges,
so it is not graceful by Rosa's parity theorem; Rosa conjectured that it is nearly-graceful,
which is contained in `rosas_conjecture`.
-/
@[category research open, AMS 5]
theorem rosas_conjecture.variants.graceful [DecidableEq V] (hG : IsTriangularCactus G)
    (ht : (G.cliqueFinset 3).card % 4 = 0 ∨ (G.cliqueFinset 3).card % 4 = 1) :
    IsGraceful G := by
  sorry

end RosasConjecture
