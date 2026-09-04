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
# Dittert conjecture

The Dittert conjecture (or Dittert–Hajek conjecture) concerns the maximum of the function
$$
\phi(A) = \prod_{i=1}^{n}\Big(\sum_{j=1}^{n} a_{ij}\Big)
  + \prod_{j=1}^{n}\Big(\sum_{i=1}^{n} a_{ij}\Big) - \operatorname{per}(A)
$$
over the set $K_n$ of real $n \times n$ matrices $A = [a_{ij}]$ with nonnegative entries and
$\sum_{i=1}^{n} \sum_{j=1}^{n} a_{ij} = n$. It asserts that $\phi$ is (uniquely) maximized at
$A = (1/n) J_n$, where $J_n$ is the $n \times n$ matrix with all entries equal to $1$.

*References:*
- [Wikipedia, Dittert conjecture](https://en.wikipedia.org/wiki/Dittert_conjecture)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- G.-S. Cheon, I. M. Wanless, *Some results towards the Dittert conjecture on permanents*,
  Linear Algebra Appl. 436 (2012), 791–801.
  [doi:10.1016/j.laa.2010.08.041](https://doi.org/10.1016/j.laa.2010.08.041)
-/

open Finset

namespace DittertConjecture

/-- The set $K_n$ of real $n \times n$ matrices with nonnegative entries whose entries sum
to $n$. -/
def K (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | (∀ i j, 0 ≤ A i j) ∧ ∑ i, ∑ j, A i j = n}

/-- The Dittert function
$\phi(A) = \prod_{i}\big(\sum_{j} a_{ij}\big) + \prod_{j}\big(\sum_{i} a_{ij}\big)
- \operatorname{per}(A)$
of a real $n \times n$ matrix $A = [a_{ij}]$: the product of the row sums, plus the product of
the column sums, minus the permanent. -/
noncomputable def dittertFun {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∏ i, ∑ j, A i j + ∏ j, ∑ i, A i j - A.permanent

local notation "φ" => dittertFun

/-- The $n \times n$ matrix $J_n$ with all entries equal to $1$. -/
def J (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun _ _ => 1

/--
**Dittert conjecture.** Let $n \geq 1$ and let $A = [a_{ij}]$ be a real $n \times n$ matrix with
nonnegative entries and $\sum_{i=1}^{n} \sum_{j=1}^{n} a_{ij} = n$. Then the function
$$
\phi(A) = \prod_{i=1}^{n}\Big(\sum_{j=1}^{n} a_{ij}\Big)
  + \prod_{j=1}^{n}\Big(\sum_{i=1}^{n} a_{ij}\Big) - \operatorname{per}(A)
$$
is uniquely maximized when $A = (1/n) J_n$, where $J_n$ is the $n \times n$ matrix with all
entries equal to $1$. That is, $\phi(A) \le \phi((1/n) J_n) = 2 - n!/n^n$ for every such $A$,
with equality only if $A = (1/n) J_n$.

The hypothesis $n \geq 1$ matches the source, whose statement involves $1/n$; for $n = 0$ the
statement is trivial.
-/
theorem dittert_conjecture (n : ℕ) (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ K n) :
    φ A ≤ φ ((1 / n : ℝ) • J n) ∧
      (φ A = φ ((1 / n : ℝ) • J n) → A = (1 / n : ℝ) • J n) := by
  sorry

end DittertConjecture

theorem DittertConjecture.dittert_conjecture.disproof : ¬ (type_of% @DittertConjecture.dittert_conjecture) := sorry
