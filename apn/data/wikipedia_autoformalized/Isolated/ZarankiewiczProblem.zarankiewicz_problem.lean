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

/--
**Zarankiewicz problem, conjectured asymptotics.** With the convention $s \le t$, it is
conjectured that for all constant values of $s, t$,
$$z(n, n; s, t) = \Theta\left(n^{2 - 1/s}\right)$$
as $n \to \infty$, where the implied constants may depend on $s$ and $t$.

The upper bound $z(n, n; s, t) = O(n^{2 - 1/s})$ is the Kővári–Sós–Turán theorem [KST54], so
the open content is the matching lower bound $z(n, n; s, t) = \Omega(n^{2 - 1/s})$. We assume
$s \ge 2$: the case $s = 1$ is trivial and $s = 0$ is degenerate.
-/
theorem zarankiewicz_problem (s t : ℕ) (hs : 2 ≤ s) (hst : s ≤ t) :
    (fun n : ℕ => (zarankiewiczNumber n n s t : ℝ)) =Θ[atTop]
      fun n : ℕ => (n : ℝ) ^ (2 - 1 / (s : ℝ)) := by
  sorry

end ZarankiewiczProblem

theorem ZarankiewiczProblem.zarankiewicz_problem.disproof : ¬ (type_of% @ZarankiewiczProblem.zarankiewicz_problem) := sorry
