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
# Hadwiger conjecture (graph theory)

The Hadwiger conjecture relates the chromatic number of a graph to its clique minors: if a
finite loopless graph $G$ has no $K_t$ minor, then $\chi(G) < t$. Equivalently, every graph $G$
satisfies $\chi(G) \le h(G)$, where $h(G)$ is the Hadwiger number of $G$ (the largest $t$ such
that $K_t$ is a minor of $G$).

The conjecture was made by Hadwiger in 1943 [Ha43]. It is known for $t \le 6$; the case $t = 5$
is equivalent to the four color theorem (Wagner, 1937) and the case $t = 6$ was proved by
Robertson, Seymour and Thomas [RST93]. It is open for every $t > 6$.

Mathlib has no notion of graph minor, so this file defines one via branch sets (minor models).

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Hadwiger conjecture (graph theory)](https://en.wikipedia.org/wiki/Hadwiger_conjecture_%28graph_theory%29)
- [Ha43] Hadwiger, H., *Über eine Klassifikation der Streckenkomplexe*. Vierteljschr.
  Naturforsch. Ges. Zürich 88 (1943), 133–142.
- [RST93] Robertson, N., Seymour, P. and Thomas, R., *Hadwiger's conjecture for $K_6$-free
  graphs*. Combinatorica 13 (1993), 279–361.
-/

namespace HadwigerConjecture2

open SimpleGraph

variable {V W : Type*}

/--
A graph `H` is a *minor* of a graph `G` if `G` contains a model of `H`: a family of pairwise
disjoint vertex sets `f w` of `G` (the *branch sets*), one for each vertex `w` of `H`, such that
every branch set induces a connected (in particular nonempty) subgraph of `G`, and whenever
`w₁` and `w₂` are adjacent in `H` some vertex of `f w₁` is adjacent in `G` to some vertex of
`f w₂`.

Equivalently, `H` is isomorphic to a graph obtained from a subgraph of `G` by contracting edges
(each branch set is contracted to a single vertex).
-/
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ f : W → Set V, (∀ w, (G.induce (f w)).Connected) ∧
    (Pairwise fun w₁ w₂ => Disjoint (f w₁) (f w₂)) ∧
    ∀ w₁ w₂, H.Adj w₁ w₂ → ∃ v₁ ∈ f w₁, ∃ v₂ ∈ f w₂, G.Adj v₁ v₂

/-- Every graph is a minor of itself: take every branch set to be a single vertex. -/
@[category API, AMS 5]
theorem isMinor_refl (G : SimpleGraph V) : IsMinor G G :=
  ⟨fun v => {v}, fun v => by simp, fun v w hvw => by simpa,
    fun v w h => ⟨v, rfl, w, rfl, h⟩⟩

/-- A minor of a subgraph of `G` is a minor of `G`. -/
@[category API, AMS 5]
theorem IsMinor.of_le {K : SimpleGraph W} {G G' : SimpleGraph V} (hG : G ≤ G')
    (h : IsMinor K G) : IsMinor K G' := by
  obtain ⟨f, hconn, hdisj, hadj⟩ := h
  refine ⟨f, fun w => (hconn w).mono fun _ _ h => hG h, hdisj, fun w₁ w₂ hw => ?_⟩
  obtain ⟨v₁, hv₁, v₂, hv₂, hv⟩ := hadj w₁ w₂ hw
  exact ⟨v₁, hv₁, v₂, hv₂, hG hv⟩

/--
The complete graph on zero vertices is a minor of every graph. In particular the case $t = 0$
of the Hadwiger conjecture holds vacuously.
-/
@[category test, AMS 5]
theorem isMinor_completeGraph_zero (G : SimpleGraph V) : IsMinor (completeGraph (Fin 0)) G :=
  ⟨Fin.elim0, fun w => w.elim0, fun w => w.elim0, fun w => w.elim0⟩

/-- A graph has a $K_1$ minor if and only if it has a vertex. -/
@[category test, AMS 5]
theorem isMinor_completeGraph_one_iff (G : SimpleGraph V) :
    IsMinor (completeGraph (Fin 1)) G ↔ Nonempty V := by
  constructor
  · rintro ⟨f, hf, -, -⟩
    obtain ⟨⟨v, -⟩⟩ := (hf 0).nonempty
    exact ⟨v⟩
  · rintro ⟨v⟩
    refine ⟨fun _ => {v}, fun _ => by simp, fun i j hij => (hij (Subsingleton.elim i j)).elim,
      fun i j h => ?_⟩
    exact absurd (Subsingleton.elim i j) h.ne

/-- A graph has a $K_2$ minor if and only if it has an edge. -/
@[category test, AMS 5]
theorem isMinor_completeGraph_two_iff (G : SimpleGraph V) :
    IsMinor (completeGraph (Fin 2)) G ↔ ∃ v w, G.Adj v w := by
  constructor
  · rintro ⟨f, -, -, hadj⟩
    obtain ⟨v, -, w, -, hvw⟩ := hadj 0 1 (by decide)
    exact ⟨v, w, hvw⟩
  · rintro ⟨v, w, hvw⟩
    refine ⟨![{v}, {w}], fun i => by fin_cases i <;> simp, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [hvw.ne, hvw.ne.symm]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [hvw.symm]

/-- A graph with fewer than `t` vertices has no `K_t` minor. -/
@[category API, AMS 5]
theorem not_isMinor_completeGraph_of_card_lt [Fintype V] (G : SimpleGraph V) {t : ℕ}
    (ht : Fintype.card V < t) : ¬ IsMinor (completeGraph (Fin t)) G := by
  rintro ⟨B, hconn, hdisj, -⟩
  have hne : ∀ i, (B i).Nonempty := fun i =>
    Set.nonempty_coe_sort.mp (hconn i).nonempty
  choose f hf using hne
  have hinj : Function.Injective f := fun i j hij => by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) (hf i) (hij ▸ hf j)
  have := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at this
  omega

/--
**Hadwiger conjecture.** For every finite loopless graph $G$ and every positive integer $t$, if
$G$ has no $K_t$ minor, then its chromatic number satisfies $\chi(G) < t$.

Equivalently, if every proper coloring of $G$ uses at least $k$ colors, then $G$ contains $k$
pairwise disjoint connected subgraphs such that each pair of them is joined by an edge, i.e. $G$
has a $K_k$ minor. In algebraic form: $\chi(G) \le h(G)$, where $h(G)$ is the Hadwiger number of
$G$ (the largest $k$ such that $K_k$ is a minor of $G$).

A `SimpleGraph` is loopless by definition, and parallel edges affect neither the chromatic number
nor the existence of a $K_t$ minor. The case $t = 0$ is degenerate: $K_0$ is a minor of every
graph (`isMinor_completeGraph_zero`).
-/
@[category research open, AMS 5]
theorem hadwiger_conjecture_2 [Fintype V] (G : SimpleGraph V) (t : ℕ) (ht : 0 < t)
    (hG : ¬ IsMinor (completeGraph (Fin t)) G) : G.chromaticNumber < t := by
  sorry

end HadwigerConjecture2
