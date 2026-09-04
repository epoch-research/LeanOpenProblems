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
# Recamán's sequence

Recamán's sequence $a_0, a_1, a_2, \ldots$ is defined by $a_0 = 0$ and, for $n \geq 1$,
$$a_n = \begin{cases}
  a_{n-1} - n & \text{if } a_{n-1} - n > 0 \text{ and }
    a_{n-1} - n \notin \{a_0, \ldots, a_{n-1}\}, \\
  a_{n-1} + n & \text{otherwise.}
\end{cases}$$
Its first terms are $0, 1, 3, 6, 2, 7, 13, 20, 12, 21, 11, 22, 10, 23, 9, 24, 8, 25, 43, 62, 42,
\ldots$ (OEIS A005132). All terms are nonnegative, but the sequence is not a permutation of
$\mathbb{N}$: for instance $a_{20} = a_{24} = 42$.

Neil Sloane conjectured that every nonnegative integer appears in the sequence. This is open.

*References:*
* [Wikipedia: Recamán's sequence](https://en.wikipedia.org/wiki/Recam%C3%A1n%27s_sequence)
* [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [OEIS A005132](https://oeis.org/A005132)
-/

namespace RecamansSequence

/--
Recamán's sequence $a_0, a_1, a_2, \ldots$: `recaman 0 = 0`, and `recaman (n + 1)` is
`recaman n - (n + 1)` if this difference is positive and is not one of the earlier terms
`recaman 0, …, recaman n`; otherwise `recaman (n + 1) = recaman n + (n + 1)`.

The condition `n + 1 < recaman n` says that the integer $a_n - (n + 1)$ is positive, so the
truncated subtraction `recaman n - (n + 1)` on `ℕ` is exact in the first branch. The quantifier
over `i : Fin (n + 1)` ranges over exactly the earlier indices $0, \ldots, n$.
-/
def recaman : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    if n + 1 < recaman n ∧ ∀ i : Fin (n + 1), recaman i ≠ recaman n - (n + 1) then
      recaman n - (n + 1)
    else
      recaman n + (n + 1)

/--
**Recamán's sequence conjecture** (Neil Sloane): does every nonnegative integer appear in
Recamán's sequence? That is, is it true that for every $m \in \mathbb{N}$ there is an index
$n$ with $a_n = m$? Sloane conjectures that the answer is yes.
-/
@[category research open, AMS 11]
theorem recamans_sequence : answer(sorry) ↔ ∀ m : ℕ, ∃ n, recaman n = m := by
  sorry

/--
The first terms of Recamán's sequence, as listed on Wikipedia and in OEIS A005132. These exercise
both failure modes of the subtraction branch: $a_3 = 6$ since $a_2 - 3 = 0$ is not positive, and
$a_6 = 13$ since $a_5 - 6 = 1 = a_1$ already appears.
-/
@[category test, AMS 11]
theorem recaman_first_terms :
    (List.range 12).map recaman = [0, 1, 3, 6, 2, 7, 13, 20, 12, 21, 11, 22] := by
  decide +kernel

/-- Recamán's sequence is not injective: the first repeated term is $42 = a_{20} = a_{24}$. -/
@[category test, AMS 11]
theorem recaman_twenty_eq_recaman_twentyFour : recaman 20 = 42 ∧ recaman 24 = 42 := by
  native_decide

end RecamansSequence
