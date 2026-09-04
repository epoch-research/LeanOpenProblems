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
# Rota's basis conjecture

*References:*
- [Wikipedia, Rota's basis conjecture](https://en.wikipedia.org/wiki/Rota%27s_basis_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [R. Huang, G.-C. Rota, *On the relations of various conjectures on Latin squares and
  straightening coefficients*, Discrete Math. 128 (1994), 225–236](https://doi.org/10.1016/0012-365X(94)90114-7)
-/

namespace RotasBasisConjecture

/--
**Rota's basis conjecture.** Let $M$ be a matroid of rank $n$ and let $B_1, \dots, B_n$ be
$n$ pairwise disjoint bases of $M$. Then the elements of these bases can be arranged into an
$n \times n$ matrix whose $i$-th row consists exactly of the elements of $B_i$ and each of whose
columns is also a base of $M$.

Equivalently, there are $n$ disjoint bases $C_1, \dots, C_n$ of $M$ (the columns), each of which
consists of exactly one element from each of the bases $B_i$.

The matrix is a function `A : Fin n → Fin n → α`, with `i`-th row `A i` and `j`-th column
`fun i ↦ A i j`. The rank of `M` is `Matroid.eRank : ℕ∞`, so `M.eRank = n` says that every base
of `M` has exactly `n` elements. Hence `Set.range (A i) = B i` says that the `i`-th row lists the
elements of `B i` without repetition. The case `n = 0` is trivially true.
-/
@[category research open, AMS 5 15]
theorem rotas_basis_conjecture {α : Type*} (n : ℕ) (M : Matroid α) (hM : M.eRank = n)
    (B : Fin n → Set α) (hB : ∀ i, M.IsBase (B i))
    (hdisj : Pairwise fun i j ↦ Disjoint (B i) (B j)) :
    ∃ A : Fin n → Fin n → α,
      (∀ i, Set.range (A i) = B i) ∧ ∀ j, M.IsBase (Set.range fun i ↦ A i j) := by
  sorry

end RotasBasisConjecture
