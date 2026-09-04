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
# Williamson conjecture

Four symmetric circulant matrices $A$, $B$, $C$, $D$ of order $n$ with entries $\pm 1$ are
*Williamson matrices* if
$$A^2 + B^2 + C^2 + D^2 = 4n I,$$
where $I$ is the identity matrix of order $n$. Williamson showed that, in this case, the block
matrix
$$\begin{bmatrix} A & B & C & D \\ -B & A & -D & C \\ -C & D & A & -B \\ -D & -C & B & A
\end{bmatrix}$$
is a Hadamard matrix of order $4n$. This is why Williamson matrices can be used to construct
Hadamard matrices.

The **Williamson conjecture** states that Williamson matrices of order $n$ exist for every
positive integer $n$. It was disproved in 1993 by Ðoković, who showed by an exhaustive computer
search that there are no Williamson matrices of order $35$. The further counterexamples
$47$, $53$ and $59$ were found in 2008 by Holzmann, Kharaghani and Tayfeh-Rezaie.

*References:*
- [Wikipedia, Williamson conjecture](https://en.wikipedia.org/wiki/Williamson_conjecture)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- J. Williamson, *Hadamard's determinant theorem and the sum of four squares*,
  Duke Math. J. 11 (1944),
  [doi:10.1215/S0012-7094-44-01108-7](https://doi.org/10.1215/S0012-7094-44-01108-7)
- D. Ž. Ðoković, *Williamson matrices of order $4n$ for $n = 33, 35, 39$*,
  Discrete Math. 115 (1993),
  [doi:10.1016/0012-365X(93)90495-F](https://doi.org/10.1016/0012-365X(93)90495-F)
- W. H. Holzmann, H. Kharaghani, B. Tayfeh-Rezaie, *Williamson matrices up to order 59*,
  Des. Codes Cryptogr. 46 (2008),
  [doi:10.1007/s10623-007-9163-5](https://doi.org/10.1007/s10623-007-9163-5)
-/

namespace WilliamsonConjecture

/--
A square matrix `M` of order `n` is a *symmetric circulant sign matrix* if all of its entries
are $\pm 1$, it is symmetric, and it is circulant (i.e. `M = Matrix.circulant v` for some
vector `v`).
-/
def IsSymmCirculantSign {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, M i j = 1 ∨ M i j = -1) ∧ M.IsSymm ∧ ∃ v : Fin n → ℤ, M = Matrix.circulant v

/--
Four matrices `A`, `B`, `C`, `D` of order `n` are *Williamson matrices* if each of them is a
symmetric circulant matrix with entries $\pm 1$ and they satisfy
$$A^2 + B^2 + C^2 + D^2 = 4n I,$$
where $I$ is the identity matrix of order $n$.
-/
structure IsWilliamson {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℤ) : Prop where
  /-- `A` is a symmetric circulant matrix with entries $\pm 1$. -/
  isSymmCirculantSign_A : IsSymmCirculantSign A
  /-- `B` is a symmetric circulant matrix with entries $\pm 1$. -/
  isSymmCirculantSign_B : IsSymmCirculantSign B
  /-- `C` is a symmetric circulant matrix with entries $\pm 1$. -/
  isSymmCirculantSign_C : IsSymmCirculantSign C
  /-- `D` is a symmetric circulant matrix with entries $\pm 1$. -/
  isSymmCirculantSign_D : IsSymmCirculantSign D
  /-- The defining identity $A^2 + B^2 + C^2 + D^2 = 4n I$. -/
  sq_add_sq_add_sq_add_sq :
    A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = (4 * n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)

/--
There are no Williamson matrices of order $35$ (Ðoković, 1993). This is the counterexample that
disproved the Williamson conjecture.
-/
theorem williamson_conjecture.variants.«35» :
    ¬ ∃ A B C D : Matrix (Fin 35) (Fin 35) ℤ, IsWilliamson A B C D := by
  sorry

end WilliamsonConjecture

theorem WilliamsonConjecture.williamson_conjecture.variants.«35».disproof : ¬ (type_of% @WilliamsonConjecture.williamson_conjecture.variants.«35») := sorry
