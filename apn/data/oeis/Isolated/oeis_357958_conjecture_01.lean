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

open Nat Finset

/--
A005259: The Apéry number sequence $A(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k}^2$.
-/
def A005259_seq (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k) ^ 2

/--
A005258: The related Apéry number sequence $C(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k}$.
-/
def A005258_seq (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k)

/--
A357958: $a(n) = 5 \cdot A005259(n) + 14 \cdot A005258(n-1)$.
The sequence is indexed from $n=1$.
-/
def a (n : ℕ) : ℕ :=
  5 * A005259_seq n + 14 * A005258_seq (n - 1)

/--
The sequence u(n) defined by u(n) = A005259(n)^25 * A005258(n-1)^14, used in Conjecture 3.
-/
def u (n : ℕ) : ℕ :=
  (A005259_seq n) ^ 25 * (A005258_seq (n - 1)) ^ 14

/--
OEIS A357958 Conjecture 1:
a(p) ≡ a(1) (mod p^5) for all primes p ≥ 5.
-/
theorem oeis_357958_conjecture_01 :
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p → (a p) ≡ (a 1) [MOD p^5] :=
by sorry

theorem oeis_357958_conjecture_01.disproof : ¬ (type_of% @oeis_357958_conjecture_01) := sorry
