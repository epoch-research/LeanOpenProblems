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
# Bondy's conjecture on longest cycles in highly connected graphs

*References:*
- [arxiv/2606.03696](https://arxiv.org/abs/2606.03696)
  **Longest cycles and Dirac-type results in highly connected graphs**
  by *Jie Ma, Bo Ning, Ziyuan Zhao*, where this is Conjecture 1.
- [Bo80] Bondy, J. A., Longest paths and cycles in graphs of high degree. (1980).

Take a `k`-connected graph with a large minimum degree. Bondy says that the graph outside any
longest cycle holds no long path.

The case `k = 1` is Dirac's theorem and the case `k = 2` is the theorem of Nash-Williams. The
case `k = 3` is proved. The cases `k ≥ 4` are open.
-/

open SimpleGraph

namespace Arxiv.«2606.03696»

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The set of vertices that a walk does not touch. For a longest cycle `C` this set carries
the graph `G - V(C)` of the conjecture. -/
def offWalk {a b : V} {G : SimpleGraph V} (w : G.Walk a b) : Set V :=
  {v | v ∉ w.support}

/--
**Conjecture 1 (Bondy, 1980).** Let $k \geq 1$ and let $G$ be a $k$-connected graph on $n$
vertices. If $\delta(G) \geq \frac{n + k(k-1)}{k+1}$, then for every longest cycle $C$ of $G$,
every path in $G - V(C)$ has at most $k-1$ vertices.

The bound on the number of vertices of a path is written as `+ 1 ≤ k` rather than `≤ k - 1`,
because subtraction on `ℕ` is truncated. The two forms agree for `k ≥ 1`.

A longest cycle is a cycle whose length is the circumference of `G`.
-/
theorem bondy_conjecture :
    ∀ (k : ℕ), 1 ≤ k → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], IsKConnected G k →
      ((Fintype.card V : ℝ) + k * (k - 1)) / (k + 1) ≤ G.minDegree →
      ∀ (a : V) (C : G.Walk a a), C.IsCycle → C.length = G.circumference →
      ∀ (u v : offWalk C) (P : (G.induce (offWalk C)).Walk u v), P.IsPath →
        P.support.length + 1 ≤ k := by
  sorry

end Arxiv.«2606.03696»

theorem Arxiv.«2606.03696».bondy_conjecture.disproof : ¬ (type_of% @Arxiv.«2606.03696».bondy_conjecture) := sorry
