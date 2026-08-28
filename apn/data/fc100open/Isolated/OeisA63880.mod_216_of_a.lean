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
# Conjectures associated with A063880

A063880 lists numbers $n$ such that $\sigma(n) = 2 \cdot \text{usigma}(n)$, where $\sigma(n)$ is the
sum of all divisors and $\text{usigma}(n)$ is the sum of unitary divisors.

Equivalently, these are numbers whose unitary and non-unitary divisors have equal sum.

The conjectures state that all members satisfy $n \equiv 108 \pmod{216}$, and that all
primitive terms (those whose proper divisors aren't in the sequence) are powerful numbers,
with $108$ being the only primitive term.

*References:* [A063880](https://oeis.org/A063880)
-/

open scoped ArithmeticFunction.sigma

namespace OeisA63880

/-- The set of unitary divisors of $n$: divisors $d$ such that $\gcd(d, n/d) = 1$. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ n.divisors | d.Coprime (n / d)}

/-- The sum of unitary divisors of $n$, denoted $\text{usigma}(n)$. -/
def usigma (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

/-- A number $n$ is in the sequence A063880 if $\sigma(n) = 2 \cdot \text{usigma}(n)$. -/
def a (n : ℕ) : Prop :=
  0 < n ∧ σ 1 n = 2 * usigma n

/-- The set of numbers in the sequence A063880. -/
def A : Set ℕ := {n | a n}

/-- A term $n$ is primitive if no proper divisor of $n$ is in the sequence. -/
abbrev isPrimitiveTerm (n : ℕ) : Prop := A.IsPrimitive n

/-- All members of the sequence satisfy $n \equiv 108 \pmod{216}$. -/
theorem mod_216_of_a {n : ℕ} (h : a n) : n % 216 = 108 := by
  sorry

end OeisA63880

theorem OeisA63880.mod_216_of_a.disproof : ¬ (type_of% @OeisA63880.mod_216_of_a) := sorry
