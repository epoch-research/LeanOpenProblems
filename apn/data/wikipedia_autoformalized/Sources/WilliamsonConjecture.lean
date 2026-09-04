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

/-- Williamson matrices of order $1$ exist: take $A = B = C = D = (1)$. -/
@[category test, AMS 5 15]
theorem isWilliamson_one : IsWilliamson (n := 1) 1 1 1 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | exact ⟨fun i j => by fin_cases i; fin_cases j; simp, Matrix.isSymm_one,
        ![1], by ext i j; fin_cases i; fin_cases j; simp⟩
    | (ext i j; fin_cases i; fin_cases j; simp)

/--
Williamson matrices of order $3$ exist: take $A = J$ (the all-ones matrix) and
$B = C = D = J - 2I$, so that $A^2 = 3J$ and $B^2 = C^2 = D^2 = 4I - J$.
-/
@[category test, AMS 5 15]
theorem isWilliamson_three :
    IsWilliamson (Matrix.circulant ![1, 1, 1]) (Matrix.circulant ![-1, 1, 1])
      (Matrix.circulant ![-1, 1, 1]) (Matrix.circulant ![-1, 1, 1]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact ⟨fun i j => by fin_cases i <;> fin_cases j <;> decide,
        Matrix.circulant_isSymm_iff.mpr (by decide), _, rfl⟩
    | (ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [sq, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sub_def, Fin.neg_def,
          Matrix.one_apply])

/--
**Williamson conjecture.** Williamson matrices of order $n$ exist for all positive integers
$n$, i.e. for every $n \ge 1$ there are symmetric circulant $\pm 1$ matrices $A$, $B$, $C$, $D$
of order $n$ with $A^2 + B^2 + C^2 + D^2 = 4n I$.

This is false: Ðoković (1993) showed that there are no Williamson matrices of order $35$, so
the statement is recorded here in its negated form.
-/
@[category research solved, AMS 5 15]
theorem williamson_conjecture :
    ¬ ∀ n : ℕ, 0 < n → ∃ A B C D : Matrix (Fin n) (Fin n) ℤ, IsWilliamson A B C D := by
  sorry

/--
There are no Williamson matrices of order $35$ (Ðoković, 1993). This is the counterexample that
disproved the Williamson conjecture.
-/
@[category research solved, AMS 5 15]
theorem williamson_conjecture.variants.«35» :
    ¬ ∃ A B C D : Matrix (Fin 35) (Fin 35) ℤ, IsWilliamson A B C D := by
  sorry

/--
There are no Williamson matrices of order $n$ for $n \in \{35, 47, 53, 59\}$ (Ðoković, 1993;
Holzmann, Kharaghani and Tayfeh-Rezaie, 2008).
-/
@[category research solved, AMS 5 15]
theorem williamson_conjecture.variants.known_counterexamples :
    ∀ n ∈ ({35, 47, 53, 59} : Finset ℕ),
      ¬ ∃ A B C D : Matrix (Fin n) (Fin n) ℤ, IsWilliamson A B C D := by
  sorry

end WilliamsonConjecture
