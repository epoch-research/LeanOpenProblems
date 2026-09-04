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
# Integer factorization

Integer factorization is the problem of splitting a composite integer $n$ into a product
of smaller integers. Wikipedia's list of unsolved problems in mathematics asks:

> Can integer factorization be done in polynomial time?

Following the Wikipedia article, this asks whether there is a deterministic (classical)
algorithm which factors every $b$-bit integer $n$ in worst-case time $O(b^k)$ for some
constant $k$, i.e. polynomial in the bit-length of $n$ and not in $n$ itself. No such
algorithm is known, and it is generally suspected that none exists. The general number field
sieve, the best published classical algorithm, runs in sub-exponential but super-polynomial
time. Shor's algorithm factors in polynomial time on a quantum computer, which does not answer
the question.

Algorithms are modelled by the deterministic Turing machines `Turing.FinTM2` of Mathlib,
with input and output written in binary (`Computability.finEncodingNatBool`), so that
`Turing.TM2ComputableInPolyTime` bounds the running time by a polynomial in the bit-length
of the input. This is the same notion of polynomial time used for the class `P` in
`FormalConjectures.Millenium.PvsNP`.

*References:*
- [Wikipedia, Integer factorization](https://en.wikipedia.org/wiki/Integer_factorization)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
-/

open Computability Turing

namespace IntegerFactorization

/--
**Integer factorization in polynomial time.**

Can integer factorization be done in polynomial time? That is, does there exist a
deterministic Turing machine which, on input a composite integer $n$ written in binary
($b$ bits), halts after at most $p(b)$ steps for a fixed polynomial $p$ and outputs a
nontrivial factor $d$ of $n$, i.e. $d \mid n$ and $1 < d < n$?

The machine computes a total function `f : ℕ → ℕ`; only its values on composite inputs are
constrained. Finding one nontrivial factor is polynomial-time equivalent to computing the
full prime factorization of $n$, by iterating on the factors.
-/
theorem integer_factorization :
    ∃ f : ℕ → ℕ,
      Nonempty (TM2ComputableInPolyTime finEncodingNatBool finEncodingNatBool f) ∧
      ∀ n, n.Composite → f n ∣ n ∧ 1 < f n ∧ f n < n := by
  sorry

end IntegerFactorization

theorem IntegerFactorization.integer_factorization.disproof : ¬ (type_of% @IntegerFactorization.integer_factorization) := sorry
