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
# Szymanski's conjecture

Szymanski's conjecture states that every permutation on the $n$-dimensional doubly-directed
hypercube graph can be routed with edge-disjoint paths.

The doubly-directed hypercube is obtained from the hypercube graph $Q_n$ by replacing every edge
with two arcs, one in each direction. We model it using the undirected graph
`SimpleGraph.hypercube n`: a directed path in the doubly-directed hypercube is a path
(`SimpleGraph.Walk.IsPath`) in `hypercube n`, and the arcs it uses are its darts
(`SimpleGraph.Walk.darts`). Two paths use the same edge in the same direction exactly when they
share a dart, so the two opposite arcs of one edge may be used by two different paths.

*References:*
- [Wikipedia, Szymanski's conjecture](https://en.wikipedia.org/wiki/Szymanski%27s_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Sz89] Szymanski, T. H., *On the permutation capability of a circuit-switched hypercube*.
  Proc. Internat. Conf. on Parallel Processing (1989), 103-110.
- [Lu90] Lubiw, A., *Counterexample to a conjecture of Szymanski on hypercube routing*.
  Inform. Process. Lett. 35 (1990), 57-61.
- [BFH01] Baudon, O., Fertin, G., Havel, I., *Routing permutations and 2-1 routing requests in
  the hypercube*. Discrete Applied Mathematics 113 (2001), 43-58.
-/

open SimpleGraph

namespace SzymanskisConjecture

/--
**Szymanski's conjecture.** Every permutation on the $n$-dimensional doubly-directed hypercube
graph can be routed with edge-disjoint paths. That is, if the permutation $\sigma$ matches each
vertex $v$ of the hypercube $Q_n$ to the vertex $\sigma(v)$, then for each $v$ there is a path in
$Q_n$ from $v$ to $\sigma(v)$ such that no two paths for two different vertices $u$ and $v$ use the
same edge in the same direction.

The paths need not be shortest paths: Lubiw [Lu90] showed that for $n \geq 5$ some permutations
cannot be routed by edge-disjoint shortest paths. A vertex fixed by $\sigma$ is routed by the
trivial path. The conjecture has been verified by computer for $n \leq 4$ [BFH01].
-/
@[category research open, AMS 5 68]
theorem szymanskis_conjecture (n : ℕ) (σ : Equiv.Perm (Fin n → Bool)) :
    ∃ p : (v : Fin n → Bool) → (hypercube n).Walk v (σ v),
      (∀ v, (p v).IsPath) ∧ ∀ u v, u ≠ v → (p u).darts.Disjoint (p v).darts := by
  sorry

/-- The identity permutation is routed by the trivial paths. -/
@[category test, AMS 5 68]
theorem szymanskis_conjecture_one (n : ℕ) :
    ∃ p : (v : Fin n → Bool) → (hypercube n).Walk v ((1 : Equiv.Perm (Fin n → Bool)) v),
      (∀ v, (p v).IsPath) ∧ ∀ u v, u ≠ v → (p u).darts.Disjoint (p v).darts :=
  ⟨fun _ => Walk.nil, fun _ => Walk.IsPath.nil, fun _ _ _ => by simp⟩

/-- The transposition of the two vertices of $Q_1$ is routed by the two opposite arcs of its
unique edge. -/
@[category test, AMS 5 68]
theorem szymanskis_conjecture_swap :
    ∃ p : (v : Fin 1 → Bool) →
      (hypercube 1).Walk v (Equiv.swap (fun _ => false) (fun _ => true) v),
      (∀ v, (p v).IsPath) ∧ ∀ u v, u ≠ v → (p u).darts.Disjoint (p v).darts := by
  have h : ∀ v : Fin 1 → Bool,
      (hypercube 1).Adj v (Equiv.swap (fun _ => false) (fun _ => true) v) := by
    simp only [hypercube_adj]
    decide
  refine ⟨fun v => Walk.cons (h v) Walk.nil, fun v => ?_, fun u v huv => ?_⟩
  · simp [Walk.cons_isPath_iff, (h v).ne]
  · simp [List.Disjoint, huv]

end SzymanskisConjecture
