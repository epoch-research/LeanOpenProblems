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
# Catalan–Dickson conjecture on aliquot sequences

The *aliquot sum* of $n$ is $s(n) = \sigma(n) - n$, the sum of the proper divisors of $n$.
The *aliquot sequence* of a positive integer $k$ is $s_0 = k$, $s_n = s(s_{n-1})$. If the sequence
reaches a prime it continues with $1$ and then $0$; following the Wikipedia article we use the
convention $s(0) = 0$, so that every aliquot sequence is infinite and a terminating sequence is
eventually constant equal to $0$.

The **Catalan–Dickson conjecture** states that every aliquot sequence ends in one of these ways:
with a prime number (and then $1$, $0$), with a perfect number, or in a cycle of amicable or
sociable numbers. In other words, no aliquot sequence is infinite but non-repeating.
Guy and Selfridge believed the conjecture to be false, i.e. that some aliquot sequence is
unbounded; this is the negation of the statement below.

*References:*
* [Wikipedia, Aliquot sequence](https://en.wikipedia.org/wiki/Aliquot_sequence%23Catalan-Dickson_conjecture)
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [OEIS A131884](https://oeis.org/A131884)
-/

namespace CatalanDicksonConjectureOnAliquotSequences

open Function

/--
The aliquot sum $s(n) = \sigma(n) - n$ of $n$: the sum of the proper divisors of $n$.
Since `Nat.properDivisors 0 = ∅`, this gives `aliquotSum 0 = 0`, which is the convention used in
the Wikipedia article to make every aliquot sequence infinite.
-/
def aliquotSum (n : ℕ) : ℕ :=
  ∑ d ∈ n.properDivisors, d

@[category test, AMS 11]
theorem aliquotSum_zero : aliquotSum 0 = 0 := by
  decide

@[category test, AMS 11]
theorem aliquotSum_one : aliquotSum 1 = 0 := by
  decide

/-- The aliquot sum of `n` is `1` if and only if `n` is prime. -/
@[category API, AMS 11]
theorem aliquotSum_eq_one_iff {n : ℕ} : aliquotSum n = 1 ↔ n.Prime :=
  Nat.sum_properDivisors_eq_one_iff_prime

/-- A positive integer is perfect if and only if it is a fixed point of `aliquotSum`. -/
@[category API, AMS 11]
theorem perfect_iff_aliquotSum_eq {n : ℕ} (hn : 0 < n) : n.Perfect ↔ aliquotSum n = n :=
  Nat.perfect_iff_sum_properDivisors hn

/-- The aliquot sequence of $10$ is $10, 8, 7, 1, 0, 0, \dots$ -/
@[category test, AMS 11]
theorem aliquotSum_iterate_ten :
    aliquotSum 10 = 8 ∧ aliquotSum^[2] 10 = 7 ∧ aliquotSum^[3] 10 = 1 ∧
      aliquotSum^[4] 10 = 0 := by
  decide

/-- The aliquot sequence of $220$ is the amicable cycle $220, 284, 220, 284, \dots$ -/
@[category test, AMS 11]
theorem aliquotSum_iterate_two_hundred_twenty :
    aliquotSum 220 = 284 ∧ aliquotSum 284 = 220 := by
  decide

/--
**Catalan–Dickson conjecture.**
For every positive integer $k$, the aliquot sequence $k, s(k), s(s(k)), \dots$ (with the
convention $s(0) = 0$) is eventually periodic: some term $s^{m}(k)$ is a periodic point of the
aliquot sum map $s$, i.e. $s^{m + p}(k) = s^{m}(k)$ for some $p > 0$. Equivalently, every aliquot
sequence either terminates (reaches a prime, then $1$, then the fixed point $0$) or enters a cycle
(a perfect number, an amicable pair, or a sociable cycle), so that no aliquot sequence is infinite
but non-repeating.
-/
@[category research open, AMS 11 37]
theorem catalan_dickson_conjecture_on_aliquot_sequences (k : ℕ) (hk : 0 < k) :
    ∃ m, aliquotSum^[m] k ∈ periodicPts aliquotSum := by
  sorry

/-- The conjecture holds for $10$: the sequence reaches the fixed point $0$ after four steps. -/
@[category test, AMS 11]
theorem catalan_dickson_ten : ∃ m, aliquotSum^[m] 10 ∈ periodicPts aliquotSum :=
  ⟨4, 1, one_pos, by decide⟩

/-- The conjecture holds for $95$: the sequence is $95, 25, 6, 6, 6, \dots$ -/
@[category test, AMS 11]
theorem catalan_dickson_ninety_five : ∃ m, aliquotSum^[m] 95 ∈ periodicPts aliquotSum :=
  ⟨2, 1, one_pos, by decide⟩

/-- The conjecture holds for the amicable number $220$, which lies on a cycle of length $2$. -/
@[category test, AMS 11]
theorem catalan_dickson_two_hundred_twenty :
    ∃ m, aliquotSum^[m] 220 ∈ periodicPts aliquotSum :=
  ⟨0, 2, two_pos, by decide⟩

end CatalanDicksonConjectureOnAliquotSequences
