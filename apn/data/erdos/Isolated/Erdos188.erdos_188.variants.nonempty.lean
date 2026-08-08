/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 188

*References:*
- [erdosproblems.com/188](https://www.erdosproblems.com/188)
- [EGMRSS75] Erdős, P. and Graham, R. L. and Montgomery, P. and Rothschild, B. L. and Spencer, J.
  and Straus, E. G., Euclidean {R}amsey theorems. {II}. (1975), 529--557.
- [Ts17] Tsaturian, Sergei, A {E}uclidean {R}amsey result in the plane. Electron. J. Combin. (2017),
  Paper No. 4.35, 9.
-/

namespace Erdos188

/--
The set of numbers $k$ such that $\mathbb{R}^2$ can be red/blue coloured with no pair of red
points unit distance apart, and no $k$-term arithmetic progression of blue points with distance 1.
-/
def s := { k : ℕ | ∃ blue : Set ℂ,
  (Set.univ \ blue).Pairwise (fun c₁ c₂ => dist c₁ c₂ ≠ 1) ∧
    ¬ (∃ᵉ (bs ⊆ blue) (z) (d), ‖d‖ = 1 ∧ bs.IsAPOfLengthWith k z d) }

/--
Old and new problems and results in combinatorial number theory by Erdős & Graham (Page 14, 15):

It has been shown that there is a large $M$ so that it is possible to partition $\mathbb{E}^2$ into
two sets $A$ and $B$ so that $A$ contains no pair of points with distance 1 and $B$ contains no A.P.
of length $M$.
-/
theorem erdos_188.variants.nonempty : s.Nonempty := by
  sorry

end Erdos188
