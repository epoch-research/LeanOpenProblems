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
# Conjectures associated with A100800

Let $f(n) = n + \text{sum of the digits of } n$. If $f(n)$ is multiple of $n$ then $a(n)= f(n)$
else $a(n) = f(f(f(n)))\dots$ until one gets a multiple of $n$; $a(n) = 0$ if no such number
exists.

*References:*
- [A100800](https://oeis.org/A100800)
-/

namespace OeisA100800

open Nat Function

/-- The sum of the decimal digits of a natural number. -/
def sumDigits (n : ℕ) : ℕ := ((10).digits n).sum

/-- The function $f(n) = n + \text{sum of the digits of } n$. -/
def f (n : ℕ) : ℕ := n + sumDigits n

open Classical in
/--
a n is the first iteration of $f(n) = n + \text{sum of the digits of } n$ that is a multiple of $n$.
$a(n) = 0$ if no such number exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- P(k) holds if the (k+1)-th iteration of f is a multiple of n.
  -- k=0 corresponds to the first iteration, f(n).
  let P (k : ℕ) : Prop := n ∣ Nat.iterate f (k + 1) n

  -- We use the noncomputable definition of finding the minimum index if it exists,
  -- or returning 0 otherwise, using the standard classical definition pattern.
  dite (∃ k, P k)
    (fun h_exists =>
      let k₀ : ℕ := Nat.find h_exists
      Nat.iterate f (k₀ + 1) n)
    (fun _ => 0)

/-- A100800 Conjecture: No term is zero. -/
theorem conjecture : ∀ (n : ℕ), n ≠ 0 → a n ≠ 0 := by
  sorry

end OeisA100800
