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
# Noncototients

A *noncototient* is a positive integer $n$ that cannot be written as $m - \varphi(m)$ for a
positive integer $m$, where $\varphi$ is Euler's totient function. It is conjectured that all
noncototients are even, i.e. that no odd noncototient exists.

*References:*
- [Wikipedia, Noncototient](https://en.wikipedia.org/wiki/noncototient)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [OEIS A005278](https://oeis.org/A005278), the sequence of noncototients
- [BrSc95] Browkin, J. and Schinzel, A., On integers not of the form $n-\phi(n)$. Colloq. Math.
  (1995), 55-58.
- [Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), problem B36.

The question of whether there are infinitely many noncototients (asked by Erdős and Sierpiński,
answered by Browkin and Schinzel) is formalised as `Erdos418.erdos_418`.
-/

namespace Noncototient

/--
The *cototient* of a positive integer $m$ is $m - \varphi(m)$, where $\varphi$ is Euler's totient
function. A positive integer $n$ is a *noncototient* if it is not the cototient of any positive
integer, i.e. if the equation $m - \varphi(m) = n$ has no solution in positive integers $m$.
-/
def IsNoncototient (n : ℕ) : Prop :=
  0 < n ∧ ∀ m, 0 < m → m - m.totient ≠ n

/--
Do any odd noncototients exist?

That is, is there an odd positive integer $n$ such that $m - \varphi(m) = n$ has no solution in
positive integers $m$? It is conjectured that the answer is no, i.e. that all noncototients are
even. This would follow from the strengthening of the Goldbach conjecture that every even number
larger than $6$ is a sum of two distinct primes; see `Erdos418.erdos_418.variants.conditional`.
-/
theorem noncototient : ∃ n, Odd n ∧ IsNoncototient n := by
  sorry

end Noncototient

theorem Noncototient.noncototient.disproof : ¬ (type_of% @Noncototient.noncototient) := sorry
