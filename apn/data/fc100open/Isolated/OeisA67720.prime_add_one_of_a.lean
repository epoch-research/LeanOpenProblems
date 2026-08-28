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
import FormalConjectures.Util.ProblemImports

/-!
# Conjectures associated with A067720

A067720 lists numbers $k$ such that $\varphi(k^2 + 1) = k \cdot \varphi(k + 1)$,
where $\varphi$ is Euler's totient function.

The sequence exhibits a strong connection to primes: for almost all terms $k$,
$k + 1$ is prime. The conjecture states that $k = 8$ is the only exception.

*References:* [A067720](https://oeis.org/A067720)
-/

open Nat

namespace OeisA67720

/-- A number $k$ is in the sequence A067720 if $\varphi(k^2 + 1) = k \cdot \varphi(k + 1)$. -/
def a (k : ℕ) : Prop :=
  φ (k ^ 2 + 1) = k * φ (k + 1)

/-- For members of the sequence other than $8$, we have $k + 1$ is prime. -/
theorem prime_add_one_of_a {k : ℕ} (h : a k) (hne : k ≠ 8) : (k + 1).Prime := by
  sorry

end OeisA67720

theorem OeisA67720.prime_add_one_of_a.disproof : ¬ (type_of% @OeisA67720.prime_add_one_of_a) := sorry
