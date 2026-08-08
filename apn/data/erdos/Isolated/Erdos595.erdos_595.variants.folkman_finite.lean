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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 595

*References:*
- [erdosproblems.com/595](https://www.erdosproblems.com/595)
- [Er87] Erdős, Paul, Problems and results on set systems and hypergraphs. Extremal problems
  for finite sets (Visegrád, 1991), Bolyai Soc. Math. Stud. (1994), 217-227.
- [Fo70] Folkman, Jon, Graphs with monochromatic complete subgraphs in every edge coloring.
  SIAM J. Appl. Math. (1970), 19:340-345.
- [NeRo75] Nešetřil, Jaroslav and Rödl, Vojtěch, Type theory of partition problems of graphs.
  Recent advances in graph theory (Proc. Second Czechoslovak Sympos., Prague, 1974),
  Academia, Prague (1975), 405-412.
-/

open SimpleGraph Set

namespace Erdos595

def IsCountableUnionOfTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

/-
## Main open problem
-/

/-
## Variants and partial results
-/

/--
**Folkman–Nešetřil–Rödl (finite version) [Fo70, NeRo75]**: For every `n ≥ 1`, there exists a
graph `G` (on a finite vertex set) that contains no $K_4$ and whose edges cannot be covered by
`n` triangle-free graphs.

More precisely: for every `n : ℕ` with `1 ≤ n`, there exist a finite type `V` and a graph
`G : SimpleGraph V` with:
1. `G.CliqueFree 4` (no $K_4$), and
2. For every family `H : Fin n → SimpleGraph V` of triangle-free graphs, `G ≠ ⨆ i, H i`.

This is the finite analogue of Problem 595. The proofs of Folkman [Fo70] and Nešetřil–Rödl
[NeRo75] give different explicit constructions.
-/
theorem erdos_595.variants.folkman_finite : 
    ∀ n : ℕ, 1 ≤ n →
    ∃ (V : Type*) (_ : Fintype V) (G : SimpleGraph V),
      G.CliqueFree 4 ∧
      ∀ (H : Fin n → SimpleGraph V), (∀ i, (H i).CliqueFree 3) → G ≠ ⨆ i, H i := by
  simp only [true_iff]
  -- Folkman [Fo70] and Nešetřil–Rödl [NeRo75]: explicit construction exists.
  sorry

end Erdos595
