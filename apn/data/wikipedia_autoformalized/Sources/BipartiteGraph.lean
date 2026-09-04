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

@[category API, AMS 5]
theorem crownGraph_adj_inl_inr {α : Type*} (i j : α) :
    (crownGraph α).Adj (Sum.inl i) (Sum.inr j) ↔ i ≠ j := by
  simp [crownGraph, fromRel_adj, eq_comm]

@[category API, AMS 5]
theorem crownGraph_adj_inr_inl {α : Type*} (i j : α) :
    (crownGraph α).Adj (Sum.inr i) (Sum.inl j) ↔ i ≠ j := by
  rw [adj_comm, crownGraph_adj_inl_inr, ne_comm]

@[category API, AMS 5]
theorem crownGraph_adj_inl_inl {α : Type*} (i j : α) :
    ¬ (crownGraph α).Adj (Sum.inl i) (Sum.inl j) := by
  simp [crownGraph]

@[category API, AMS 5]
theorem crownGraph_adj_inr_inr {α : Type*} (i j : α) :
    ¬ (crownGraph α).Adj (Sum.inr i) (Sum.inr j) := by
  simp [crownGraph]

@[category API, AMS 5]
theorem crownGraph_isBipartite (α : Type*) : (crownGraph α).IsBipartite :=
  Colorable.mono_left sdiff_le (CompleteBipartiteGraph.bicoloring α α).colorable

/-- The crown graph $H_{1,1}$ has two vertices and no edges. -/
@[category test, AMS 5]
theorem crownGraph_fin_one : crownGraph (Fin 1) = ⊥ := by
  ext (i | i) (j | j) <;>
    simp [crownGraph_adj_inl_inr, crownGraph_adj_inr_inl, Fin.fin_one_eq_zero]

/-- The letters `0` and `1` alternate in the word `0101`. -/
@[category test, AMS 5 68]
theorem alternate_example : Alternate [0, 1, 0, 1] (0 : Fin 2) 1 := by
  unfold Alternate
  decide

/-- The letters `0` and `1` do not alternate in the word `0011`. -/
@[category test, AMS 5 68]
theorem not_alternate_example : ¬ Alternate [0, 0, 1, 1] (0 : Fin 2) 1 := by
  unfold Alternate
  decide

/-- The complete graph on three vertices is represented by the word `012`. -/
@[category test, AMS 5 68]
theorem isKRepresentable_top_one : IsKRepresentable (⊤ : SimpleGraph (Fin 3)) 1 :=
  ⟨[0, 1, 2], ⟨by decide, by unfold Alternate; decide⟩, by decide⟩

/-- The crown graph $H_{1,1}$ (two isolated vertices $a, b$) is represented by the word `aabb`. -/
@[category test, AMS 5 68]
theorem isKRepresentable_crownGraph_one_two : IsKRepresentable (crownGraph (Fin 1)) 2 := by
  refine ⟨[Sum.inl 0, Sum.inl 0, Sum.inr 0, Sum.inr 0], ⟨?_, ?_⟩, ?_⟩
  · rintro (i | i) <;> fin_cases i <;> simp
  · rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [Alternate, crownGraph_fin_one]
  · rintro (i | i) <;> fin_cases i <;> simp

/-- A non-empty complete graph has representation number `1`: it is represented by a permutation
of its vertices, and no graph with a vertex is represented by a word with `0` copies of each
letter. -/
@[category API, AMS 5 68]
theorem representationNumber_top (n : ℕ) :
    representationNumber (⊤ : SimpleGraph (Fin (n + 1))) = 1 := by
  have h1 : IsKRepresentable (⊤ : SimpleGraph (Fin (n + 1))) 1 := by
    refine ⟨List.finRange (n + 1), ⟨fun v => List.mem_finRange v, fun x y hxy => ?_⟩,
      fun v => List.count_eq_one_of_mem (List.nodup_finRange _) (List.mem_finRange v)⟩
    simpa [hxy, Alternate] using ((List.nodup_finRange (n + 1)).filter _).isChain
  refine le_antisymm (Nat.sInf_le h1) (Nat.one_le_iff_ne_zero.2 fun h0 => ?_)
  obtain ⟨w, ⟨hw, -⟩, hcount⟩ :=
    (Nat.sInf_eq_zero.1 h0).resolve_right (Set.Nonempty.ne_empty ⟨1, h1⟩)
  exact absurd (hcount 0) (List.count_pos_iff.2 (hw 0)).ne'

/-- A graph with at least one vertex is not `0`-representable, since a representing word must
contain every vertex. -/
@[category API, AMS 5 68]
theorem not_isKRepresentable_zero [Nonempty V] (G : SimpleGraph V) : ¬ IsKRepresentable G 0 := by
  rintro ⟨w, ⟨hmem, -⟩, hw⟩
  obtain ⟨v⟩ := ‹Nonempty V›
  exact (List.count_pos_iff.mpr (hmem v)).ne' (hw v)

/-- A `1`-uniform word is a permutation of the vertices, and a permutation represents the
complete graph: the only `1`-representable graphs are the complete graphs. -/
@[category API, AMS 5 68]
theorem eq_top_of_isKRepresentable_one (G : SimpleGraph V) (h : IsKRepresentable G 1) :
    G = ⊤ := by
  obtain ⟨w, ⟨-, h⟩, hw⟩ := h
  have hnd : w.Nodup := List.nodup_iff_count_le_one.mpr fun v => (hw v).le
  ext x y
  exact ⟨fun h => h.ne, fun hxy => (h x y hxy).mp (hnd.filter _).isChain⟩

/-- The crown graph $H_{2,2}$ (two disjoint edges $a b'$ and $b a'$) is `2`-representable, e.g. by
the word $a b' a b' a' b a' b$, where $a, b$ are the left and $a', b'$ the right vertices. -/
@[category test, AMS 5 68]
theorem isKRepresentable_crownGraph_two_two : IsKRepresentable (crownGraph (Fin 2)) 2 := by
  refine ⟨[.inl 0, .inr 1, .inl 0, .inr 1, .inr 0, .inl 1, .inr 0, .inl 1], ⟨?_, ?_⟩, ?_⟩
  · rintro (i | i) <;> fin_cases i <;> simp
  · rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [Alternate, crownGraph_adj_inl_inr, crownGraph_adj_inr_inl, crownGraph_adj_inl_inl,
        crownGraph_adj_inr_inr]
  · rintro (i | i) <;> fin_cases i <;> simp

/-- The representation number of the crown graph $H_{2,2}$ is `2`. -/
@[category test, AMS 5 68]
theorem representationNumber_crownGraph_two :
    representationNumber (crownGraph (Fin 2)) = 2 := by
  refine le_antisymm (Nat.sInf_le isKRepresentable_crownGraph_two_two)
    (le_csInf ⟨2, isKRepresentable_crownGraph_two_two⟩ ?_)
  rintro (_ | _ | k) hk
  · exact (not_isKRepresentable_zero _ hk).elim
  · have := congrArg (fun G => G.Adj (Sum.inl 0) (Sum.inr 0)) (eq_top_of_isKRepresentable_one _ hk)
    simp [crownGraph_adj_inl_inr] at this
  · omega

/--
**Glen–Kitaev–Pyatkin (2018).** For $m \ge 5$ the crown graph $H_{m,m}$ has representation
number $\lceil m/2 \rceil$. (The restriction $m \ge 5$ is needed: $H_{4,4}$ is the $3$-cube,
whose representation number is $3$.)
-/
@[category research solved, AMS 5 68]
theorem representationNumber_crownGraph (m : ℕ) (hm : 5 ≤ m) :
    representationNumber (crownGraph (Fin m)) = (m + 1) / 2 := by
  sorry

/--
Is it true that out of all bipartite graphs, crown graphs require longest word-representants?

Precisely: is it true that for every $m$ and every bipartite graph $G$ on $2m$ vertices, the
representation number of $G$ is at most that of the crown graph $H_{m,m}$ on $2m$ vertices, i.e.
$\mathcal{R}(G) \le \mathcal{R}(H_{m,m})$? A graph on $n$ vertices represented with $k$ copies
of each letter is represented by a word of length $kn$, so this says that among the bipartite
graphs on a given number of vertices the crown graph needs the longest word-representants.
Crown graphs have an even number of vertices, so only even orders are compared; a bipartite
graph on $2m + 1$ vertices is an induced subgraph of one on $2m + 2$ vertices. No lower bound on
$m$ is imposed: the comparison is with $\mathcal{R}(H_{m,m})$ itself rather than with the formula
$\lceil m/2 \rceil$, which only holds for $m \ge 5$.
-/
@[category research open, AMS 5 68]
theorem bipartite_graph :
    answer(sorry) ↔ ∀ (m : ℕ) (G : SimpleGraph (Fin (2 * m))), G.IsBipartite →
      representationNumber G ≤ representationNumber (crownGraph (Fin m)) := by
  sorry

end BipartiteGraph
