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
# Integer values of $\tan(\arctan 1 + \arctan 2 + \cdots + \arctan n)$

*References:*
- [arxiv/2607.05739](https://arxiv.org/abs/2607.05739)
  **Integer values of $\tan(\arctan 1+\arctan 2+\cdots+\arctan n)$ are rare** by *Ken Ono*
- [AMM08] T. Amdeberhan, L. A. Medina, and V. H. Moll, *Arithmetical properties of a sequence
  arising from an arctangent sum*, J. Number Theory 128 (2008), no. 6, 1807-1846.
- [TanArctan](https://github.com/AxiomMath/TanArctan), a Lean formalisation of the three
  results of [Ono26], MIT licensed. Its `P`, `A`, `B` and `x` are the definitions used
  here.
-/

open Finset

namespace Arxiv.«2607.05739»

/-- $Z_n = \prod_{k=1}^n (1 + ik)$, in the Gaussian integers. -/
def gaussProd (n : ℕ) : GaussianInt := ∏ k ∈ Finset.Icc 1 n, (⟨1, (k : ℤ)⟩ : GaussianInt)

/-- $A_n = \operatorname{Re} Z_n$. -/
def A (n : ℕ) : ℤ := (gaussProd n).re

/-- $B_n = \operatorname{Im} Z_n$. -/
def B (n : ℕ) : ℤ := (gaussProd n).im

/-- $x_n = \tan\left(\sum_{k=1}^n \arctan k\right) = B_n / A_n$. -/
noncomputable def x (n : ℕ) : ℚ := (B n : ℚ) / (A n : ℚ)

/-- $x_n$ takes an integer value.

Stated as $A_n \mid B_n$ rather than as `∃ m : ℤ, x n = m`, so that it still says the right
thing if $A_n$ were ever $0$. There $x_n$ is a pole of the tangent rather than an integer, but
`(B n : ℚ) / 0` is `0` in Lean and would count as one. The two agree whenever $A_n \neq 0$,
which holds for every $n \leq 3000$. -/
def IsIntegerValue (n : ℕ) : Prop := A n ∣ B n

instance (n : ℕ) : Decidable (IsIntegerValue n) := by unfold IsIntegerValue; infer_instance

/--
**Conjecture (Amdeberhan-Medina-Moll, 2008).** For every integer $n \geq 5$, the value
$$x_n = \tan(\arctan 1 + \arctan 2 + \cdots + \arctan n)$$
is not an integer.
-/
theorem tan_arctan_sum_not_integer :
    ∀ n : ℕ, 5 ≤ n → ¬ IsIntegerValue n := by
  sorry

/-- $\omega_n = A_n^2 + B_n^2 = \prod_{k=1}^n (1 + k^2)$, the norm of $Z_n$. -/
def omega (n : ℕ) : ℕ := (A n).natAbs ^ 2 + (B n).natAbs ^ 2

/-- The squarefree kernel $K_n$ of $\omega_n$: the product of the primes dividing it to an
odd power, so `1` when there are none. -/
def kernel (n : ℕ) : ℕ :=
  ∏ p ∈ (omega n).primeFactors.filter (fun p => Odd ((omega n).factorization p)), p

/-- $a_n = \sum_{k=1}^n \arctan(1/k)$. -/
noncomputable def angleSum (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, Real.arctan (1 / (k : ℝ))

/-- The exceptional set $E = \{n \geq 5 : |x_n| > n/2 + 1\}$. An index with $A_n = 0$ is a
pole of the tangent rather than a large value, and is counted in, reading $|x_n|$ as infinite. -/
def exceptional : Set ℕ := {n | 5 ≤ n ∧ (A n = 0 ∨ ((n : ℚ) / 2 + 1 < |x n|))}

end Arxiv.«2607.05739»
