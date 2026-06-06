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

open Nat Set

/--
A321576: $a(n)$ is the smallest $b > 1$ such that $b^n - (b-1)^n$ has all divisors $d \equiv 1 \pmod n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h_n : n > 0 then
    let S_n : Set ℕ :=
      { b | b > 1 ∧
          let k := b ^ n - (b - 1) ^ n
          ∀ (d : ℕ), d ∣ k → d ≡ 1 [MOD n] }
    -- sInf finds the smallest element of a set in a partial order, which for $\mathbb{N}$ is the minimum.
    sInf S_n
  else
    0

/--
If n is prime, then a(n) = 2. Conjecture: If n is composite, then a(n) > 2.
-/
theorem oeis_321576_conjecture_0 (n : ℕ) (hn : n > 1) :
  (n.Prime → a n = 2) ∧ (¬ n.Prime → a n > 2) :=
by sorry
