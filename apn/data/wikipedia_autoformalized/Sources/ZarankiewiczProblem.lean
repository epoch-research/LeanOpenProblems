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
# Zarankiewicz problem

The Zarankiewicz problem asks how many edges a bipartite graph on a given number of vertices can
have if it contains no complete bipartite subgraph of a given size.

The *Zarankiewicz function* $z(m, n; s, t)$ is the maximum number of edges in a bipartite graph
$G = (U \cup V, E)$ with $|U| = m$ and $|V| = n$ that contains no subgraph $K_{s,t}$ with its $s$
vertices in $U$ and its $t$ vertices in $V$. Equivalently, $z(m, n; s, t)$ is the maximum number
of $1$s in an $m \times n$ $(0,1)$-matrix that contains no $s \times t$ all-ones submatrix.
One writes $z(n; t) = z(n, n; t, t)$.

*References:*
- [Wikipedia, Zarankiewicz problem](https://en.wikipedia.org/wiki/Zarankiewicz_problem)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Co21] Conlon, D., *Some remarks on the Zarankiewicz problem*, Math. Proc. Cambridge Philos.
  Soc. 173 (2022), 155–161. [arXiv:2007.12816](https://arxiv.org/abs/2007.12816)
- [KST54] Kővári, T., Sós, V. T. and Turán, P., *On a problem of K. Zarankiewicz*,
  Colloq. Math. 3 (1954), 50–57.
-/

open Filter Asymptotics Finset

namespace ZarankiewiczProblem

/-- A set `A` of cells of an `m × n` grid, that is, the edge set of a bipartite graph with parts
`Fin m` and `Fin n`, is *`(s, t)`-biclique-free* if there are no `s` rows and `t` columns all of
whose `s * t` cells lie in `A`. In graph terms, the bipartite graph contains no subgraph
$K_{s,t}$ with its $s$ vertices in the part `Fin m` and its $t$ vertices in the part `Fin n`.
The order of `s` and `t` matters. -/
def IsBicliqueFree {m n : ℕ} (A : Finset (Fin m × Fin n)) (s t : ℕ) : Prop :=
  ∀ (S : Finset (Fin m)) (T : Finset (Fin n)), #S = s → #T = t → ¬ S ×ˢ T ⊆ A

instance {m n : ℕ} (A : Finset (Fin m × Fin n)) (s t : ℕ) :
    Decidable (IsBicliqueFree A s t) := by
  unfold IsBicliqueFree
  infer_instance

/-- The **Zarankiewicz function** $z(m, n; s, t)$: the maximum number of edges in a bipartite
graph with parts of sizes $m$ and $n$ that contains no subgraph $K_{s,t}$ with its $s$ vertices in
the part of size $m$ and its $t$ vertices in the part of size $n$. Here the bipartite graph is
encoded by its edge set `A : Finset (Fin m × Fin n)`. -/
def zarankiewiczNumber (m n s t : ℕ) : ℕ :=
  (univ.filter fun A : Finset (Fin m × Fin n) => IsBicliqueFree A s t).sup card

/-- The full `m × n` grid is not `(s, t)`-biclique-free when `s ≤ m` and `t ≤ n`. -/
@[category test, AMS 5]
theorem not_isBicliqueFree_univ {m n s t : ℕ} (hs : s ≤ m) (ht : t ≤ n) :
    ¬ IsBicliqueFree (univ : Finset (Fin m × Fin n)) s t := by
  obtain ⟨S, hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin m))) (by simpa using hs)
  obtain ⟨T, hT⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (by simpa using ht)
  exact fun h => h S T hS.2 hT.2 (subset_univ _)

/-- $z(m, n; s, t) \le mn$, since a bipartite graph with parts of sizes `m` and `n` has at most
`m n` edges. -/
@[category API, AMS 5]
theorem zarankiewiczNumber_le (m n s t : ℕ) : zarankiewiczNumber m n s t ≤ m * n := by
  refine Finset.sup_le fun A _ => ?_
  simpa using card_le_univ A

/-- $z(m, n; s, t) = mn$ when `m < s`, since then no bipartite graph with parts of sizes `m` and
`n` contains a $K_{s,t}$ with `s` vertices in the first part. -/
@[category API, AMS 5]
theorem zarankiewiczNumber_of_lt {m n s t : ℕ} (h : m < s) :
    zarankiewiczNumber m n s t = m * n := by
  refine le_antisymm (zarankiewiczNumber_le m n s t) ?_
  have hfree : IsBicliqueFree (univ : Finset (Fin m × Fin n)) s t := fun S _ hS _ _ => by
    have := card_le_univ S
    simp only [Fintype.card_fin] at this
    omega
  have hmem : (univ : Finset (Fin m × Fin n)) ∈
      univ.filter fun A : Finset (Fin m × Fin n) => IsBicliqueFree A s t :=
    mem_filter.2 ⟨mem_univ _, hfree⟩
  simpa using Finset.le_sup (f := card) hmem

/-- $z(2; 2) = 3$, achieved by a path with three edges. -/
@[category test, AMS 5]
theorem zarankiewiczNumber_two_two : zarankiewiczNumber 2 2 2 2 = 3 := by
  decide

/-- Orientation check: with one vertex on the side of size $1$ and three on the side of size $3$,
forbidding $K_{1,2}$ (one vertex on the first side, two on the second) allows only one edge,
whereas forbidding $K_{2,1}$ allows all three edges (see `zarankiewiczNumber_of_lt`). -/
@[category test, AMS 5]
theorem zarankiewiczNumber_one_three : zarankiewiczNumber 1 3 1 2 = 1 := by
  decide

/--
**Zarankiewicz problem, conjectured asymptotics.** With the convention $s \le t$, it is
conjectured that for all constant values of $s, t$,
$$z(n, n; s, t) = \Theta\left(n^{2 - 1/s}\right)$$
as $n \to \infty$, where the implied constants may depend on $s$ and $t$.

The upper bound $z(n, n; s, t) = O(n^{2 - 1/s})$ is the Kővári–Sós–Turán theorem [KST54], so
the open content is the matching lower bound $z(n, n; s, t) = \Omega(n^{2 - 1/s})$. We assume
$s \ge 2$: the case $s = 1$ is trivial and $s = 0$ is degenerate.
-/
@[category research open, AMS 5]
theorem zarankiewicz_problem (s t : ℕ) (hs : 2 ≤ s) (hst : s ≤ t) :
    (fun n : ℕ => (zarankiewiczNumber n n s t : ℝ)) =Θ[atTop]
      fun n : ℕ => (n : ℝ) ^ (2 - 1 / (s : ℝ)) := by
  sorry

/--
**Zarankiewicz problem, diagonal case.** The Zarankiewicz problem asks for tight asymptotic
bounds on the growth rate of $z(n; t) = z(n, n; t, t)$ for fixed $t$ as $n \to \infty$. The
conjectured answer (the case $s = t$ of `zarankiewicz_problem`) is
$$z(n; t) = \Theta\left(n^{2 - 1/t}\right)$$
for every fixed $t \ge 2$, where the implied constants may depend on $t$.

The upper bound $z(n; t) = O(n^{2 - 1/t})$ is the Kővári–Sós–Turán theorem [KST54]; the
matching lower bound is known only for $t = 2$ and $t = 3$.
-/
@[category research open, AMS 5]
theorem zarankiewicz_problem.variants.diagonal (t : ℕ) (ht : 2 ≤ t) :
    (fun n : ℕ => (zarankiewiczNumber n n t t : ℝ)) =Θ[atTop]
      fun n : ℕ => (n : ℝ) ^ (2 - 1 / (t : ℝ)) := by
  sorry

/--
**Zarankiewicz problem, unbalanced case** ([Co21], Question 1). Is it the case that for
any fixed $s$ and $t$ with $2 \le s \le t$ and any $m \le n^{t/s}$,
$$z(m, n; s, t) = \Omega\left(m n^{1 - 1/s}\right),$$
where the implied constant depends only on $s$ and $t$? That is, for all fixed $2 \le s \le t$
does there exist $c > 0$ such that $z(m, n; s, t) \ge c \, m n^{1 - 1/s}$ for all $m, n$ with
$m \le n^{t/s}$?

Here $n^{t/s}$ is the crossover point of the two Kővári–Sós–Turán bounds
$z(m, n; s, t) = O(m n^{1 - 1/s} + n)$ and $z(m, n; s, t) = O(n m^{1 - 1/t} + m)$, so a positive
answer would determine $z(m, n; s, t)$ up to a constant factor for all $m$ and $n$. The
orientation of $K_{s,t}$ matters here: its $s$ vertices lie in the part of size $m$ and its $t$
vertices lie in the part of size $n$. The Wikipedia article writes the range as
$m \le n^{s/t}$; the exponent $t/s$ follows [Co21].
-/
@[category research open, AMS 5]
theorem zarankiewicz_problem.variants.unbalanced :
    answer(sorry) ↔
      ∀ s t : ℕ, 2 ≤ s → s ≤ t → ∃ c : ℝ, 0 < c ∧
        ∀ m n : ℕ, (m : ℝ) ≤ (n : ℝ) ^ ((t : ℝ) / s) →
          c * (m * (n : ℝ) ^ (1 - 1 / (s : ℝ))) ≤ zarankiewiczNumber m n s t := by
  sorry

end ZarankiewiczProblem
