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

/-- The letters `0` and `1` alternate in the word `0101`. -/
@[category test, AMS 5 68]
theorem alternate_example : Alternate [(0 : Fin 2), 1, 0, 1] 0 1 := by
  unfold Alternate
  decide

/-- The letters `0` and `1` do not alternate in the word `0011`. -/
@[category test, AMS 5 68]
theorem not_alternate_example : ¬ Alternate [(0 : Fin 2), 0, 1, 1] 0 1 := by
  unfold Alternate
  decide

/-- The word `abdacdbc` represents the cycle graph on the four vertices `a, b, c, d`. -/
@[category test, AMS 5 68]
theorem represents_cycleGraph_four :
    Represents [0, 1, 3, 0, 2, 3, 1, 2] (cycleGraph 4) := by
  simp only [Represents, Alternate]
  decide

/-- Every complete graph is `1`-representable: it is represented by any permutation of its
vertices. -/
@[category test, AMS 5 68]
theorem isKRepresentable_top_one (n : ℕ) : IsKRepresentable (⊤ : SimpleGraph (Fin n)) 1 := by
  refine ⟨List.finRange n, fun v => ?_, fun v => List.mem_finRange v, fun a b hab => ?_⟩
  · exact List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange v)
  · simp only [top_adj, ne_eq, hab, not_false_eq_true, true_iff]
    exact ((List.nodup_finRange n).filter _).isChain

/-- The complete graph on `n + 1` vertices has representation number `1`. -/
@[category test, AMS 5 68]
theorem representationNumber_top (n : ℕ) :
    representationNumber (⊤ : SimpleGraph (Fin (n + 1))) = 1 := by
  apply le_antisymm
  · exact iInf₂_le 1 (isKRepresentable_top_one (n + 1))
  · refine le_iInf₂ fun k hk => ?_
    obtain ⟨w, hw, hmem, -⟩ := hk
    have := hmem 0
    rw [← List.count_pos_iff, hw 0] at this
    exact_mod_cast this

/-- A graph that is not word-representable has representation number `∞`. -/
@[category API, AMS 5 68]
theorem representationNumber_eq_top_of_not_wordRepresentable {G : SimpleGraph V}
    (hG : ¬ WordRepresentable G) : representationNumber G = ⊤ := by
  simp only [representationNumber, iInf_eq_top, ENat.coe_ne_top, imp_false, Set.mem_setOf_eq]
  exact fun k ⟨w, _, hw⟩ => hG ⟨w, hw⟩

/-- A `1`-representable graph is complete. -/
@[category API, AMS 5 68]
theorem eq_top_of_isKRepresentable_one {G : SimpleGraph V} (h : IsKRepresentable G 1) :
    G = ⊤ := by
  obtain ⟨w, hw, -, hrep⟩ := h
  ext a b
  rw [top_adj]
  refine ⟨fun h => h.ne, fun hab => (hrep a b hab).2 ?_⟩
  unfold Alternate
  set l := w.filter fun x => x = a ∨ x = b with hl
  have hmem : ∀ x ∈ l, x = a ∨ x = b := fun x hx => by simpa using (List.mem_filter.1 hx).2
  have hperm : l.Perm [a, b] := by
    rw [List.perm_iff_count]
    intro x
    by_cases hxa : x = a
    · subst hxa; simp [hl, hw, hab]
    by_cases hxb : x = b
    · subst hxb; simp [hl, hw, Ne.symm hxa]
    · rw [List.count_eq_zero.2 fun hx => (hmem x hx).elim hxa hxb]
      simp [Ne.symm hxa, Ne.symm hxb]
  obtain ⟨x, y, hxy⟩ := List.length_eq_two.1 hperm.length_eq
  rw [hxy] at hperm ⊢
  have hnd : [x, y].Nodup := hperm.nodup_iff.2 (by simp [hab])
  simpa using hnd

/-- The path on three vertices `0 - 1 - 2` is `2`-representable. -/
@[category test, AMS 5 68]
theorem isKRepresentable_pathGraph_three : IsKRepresentable (pathGraph 3) 2 :=
  ⟨[1, 0, 2, 1, 2, 0], by decide, by simp only [Represents, Alternate, pathGraph_adj]; decide⟩

/-- The path on three vertices has representation number `2`, which exceeds `⌊3 / 2⌋ = 1`. This
is one of the degenerate small cases excluded by the hypothesis `4 ≤ n` in `representation`. -/
@[category test, AMS 5 68]
theorem representationNumber_pathGraph_three : representationNumber (pathGraph 3) = 2 := by
  apply le_antisymm
  · exact iInf₂_le 2 isKRepresentable_pathGraph_three
  · refine le_iInf₂ fun k hk => ?_
    obtain ⟨w, hw, hmem, hrep⟩ := hk
    have h0 : 0 < k := by
      have := hmem 0
      rwa [← List.count_pos_iff, hw 0] at this
    have h1 : k ≠ 1 := by
      rintro rfl
      have h02 : (pathGraph 3).Adj 0 2 := by
        rw [eq_top_of_isKRepresentable_one ⟨w, hw, hmem, hrep⟩]
        decide
      simp [pathGraph_adj] at h02
    exact_mod_cast (by omega : 2 ≤ k)

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
@[category research open, AMS 5 68]
theorem representation :
    answer(sorry) ↔ ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      4 ≤ n ∧ WordRepresentable G ∧ (n / 2 : ℕ) < representationNumber G := by
  sorry

end Representation
