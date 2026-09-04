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
# Brouwer's conjecture

Brouwer's conjecture gives upper bounds for the sums of the largest eigenvalues of the
Laplacian matrix of a finite simple graph in terms of its number of edges.

*References:*
- [Wikipedia: Brouwer's conjecture](https://en.wikipedia.org/wiki/Brouwer%27s_conjecture)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- A. E. Brouwer, W. H. Haemers, *Spectra of Graphs*, Springer (2012).
- J. N. Cooper, *Constraints on Brouwer's Laplacian spectrum conjecture*,
  [arXiv:2003.03447](https://arxiv.org/abs/2003.03447)
- I. Rocha, *Brouwer's conjecture holds asymptotically almost surely*,
  [arXiv:1906.05368](https://arxiv.org/abs/1906.05368)
-/

namespace BrouwersConjecture

open Finset

/--
**Brouwer's conjecture.** Let $G$ be a finite simple undirected graph on $n$ vertices with
$m(G)$ edges, and let $\lambda_1 \ge \lambda_2 \ge \dots \ge \lambda_n$ be the eigenvalues of
its Laplacian matrix $L(G) = D(G) - A(G)$, listed in decreasing order with multiplicity. Then
for every $t = 1, \dots, n$,
$$\sum_{i=1}^{t} \lambda_i \le m(G) + \binom{t+1}{2}.$$

Here the eigenvalues are `(G.posSemidef_lapMatrix ℝ).isHermitian.eigenvalues₀`, which lists the
eigenvalues of the real symmetric matrix `G.lapMatrix ℝ` in decreasing order
(`Matrix.IsHermitian.eigenvalues₀_antitone`), indexed by `Fin n`. The sum of the `t` largest
eigenvalues is obtained by restricting along `Fin.castLE`. The case $t = 0$ is also allowed:
it reads $0 \le m(G)$ and is trivially true.
-/
theorem brouwers_conjecture {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) (ht : t ≤ Fintype.card V) :
    ∑ i : Fin t, (G.posSemidef_lapMatrix ℝ).isHermitian.eigenvalues₀ (Fin.castLE ht i) ≤
      #G.edgeFinset + (t + 1).choose 2 := by
  sorry

end BrouwersConjecture

theorem BrouwersConjecture.brouwers_conjecture.disproof : ¬ (type_of% @BrouwersConjecture.brouwers_conjecture) := sorry
