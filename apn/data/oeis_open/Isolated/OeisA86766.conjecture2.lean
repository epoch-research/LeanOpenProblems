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
# Smallest $r$ such that (concatenation of $n$, $r$ times) $\cdot 10 + 1$ is prime

$a(n)$ is the smallest $r$ where (concatenation of $n$, $r$ times with itself) $\cdot 10 + 1$
is a prime, or $0$ if no such number exists.
The number resulting from concatenating $n$, $r$ times, is
$n \cdot \sum_{i=0}^{r-1} (10^d)^i$, where $d$ is the number of digits of $n$.

*References:*
- [A086766](https://oeis.org/A086766)-/

namespace OeisA86766

/-- Sequence $a(n)$ is the smallest $r > 0$ such that the concatenation of $n$, $r$ times
with itself, multiplied by $10$ plus $1$, is prime, or $0$ if no such prime exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let ℓ : ℕ := (Nat.digits 10 n).length
    let M : ℕ := 10 ^ ℓ
    let repCatVal (r : ℕ) : ℕ := n * ∑ i ∈ Finset.range r, M ^ i
    let primeCandidate (r : ℕ) : ℕ := repCatVal r * 10 + 1
    sInf {r : ℕ | 0 < r ∧ (primeCandidate r).Prime}

/--
Conjecture: If $n$ is not of the form $10^m$ then $a(n)$ is nonzero.
- _Farideh Firoozbakht_, Jan 07 2015
-/
theorem conjecture2 (n : ℕ) (hn : 0 < n) (h : ∀ m : ℕ, n ≠ 10 ^ m) : a n ≠ 0 := by
  sorry

end OeisA86766

theorem OeisA86766.conjecture2.disproof : ¬ (type_of% @OeisA86766.conjecture2) := sorry
