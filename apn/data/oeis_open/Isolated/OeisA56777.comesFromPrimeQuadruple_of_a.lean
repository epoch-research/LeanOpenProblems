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
# Divisibility of $2^n + 1$ by $n$

A56777 lists composite numbers $n$ satisfying both $\varphi(n+12) = \varphi(n) + 12$ and
$\sigma(n+12) = \sigma(n) + 12$.

The conjectures state identities connecting A56777 and prime quadruples (A7530), as
well as congruences satisfied by the members of A56777.

*References:*
- [A56777](https://oeis.org/A56777)
-/

namespace OeisA56777

open Nat
open scoped ArithmeticFunction.sigma

/-- A composite number $n$ is in the sequence A56777 if it satisfies both
$\varphi(n+12) = \varphi(n) + 12$ and $\sigma(n+12) = \sigma(n) + 12$. -/
def A (n : ℕ) : Prop :=
  ¬n.Prime ∧ 1 < n ∧ totient (n + 12) = totient n + 12 ∧ σ 1 (n + 12) = σ 1 n + 12

/-- A number $n$ comes from a prime quadruple $(p, p+2, p+6, p+8)$ if
$n = p(p+8)$ for some prime $p$ where $p$, $p+2$, $p+6$, $p+8$ are all prime. -/
def ComesFromPrimeQuadruple (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8)

/-- All members of the sequence A56777 come from prime quadruples. -/
theorem comesFromPrimeQuadruple_of_a {n : ℕ} (h : A n) : ComesFromPrimeQuadruple n := by
  sorry

end OeisA56777

theorem OeisA56777.comesFromPrimeQuadruple_of_a.disproof : ¬ (type_of% @OeisA56777.comesFromPrimeQuadruple_of_a) := sorry
