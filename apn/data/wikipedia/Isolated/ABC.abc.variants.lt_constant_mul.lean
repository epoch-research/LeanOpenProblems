/-
Copyright 2025 The Formal Conjectures Authors.

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
# *abc* conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Abc_conjecture)
-/

namespace ABC

/--
The radical of `n` denoted is the product of the distinct prime factors of `n`.
-/
def radical (n : ℕ) : ℕ := n.primeFactors.prod id

/--
Quality `q(a, b, c)` of the triple `(a, b, c)` is defined as `q(a,b,c) = log (c) / log (rad(abc))`.
-/
noncomputable def quality (a b c : ℕ) : ℝ := (c : ℝ).log / (radical <| a * b * c : ℝ).log

/--
For every positive real number ε, there exists a constant `K_ε` such that for all triples (a, b, c) of coprime positive integers, with a + b = c we have `c < K_ε rad(abc)^(1+ε)`.
-/
theorem abc.variants.lt_constant_mul (ε : ℝ) (hε : 0 < ε) : ∃ K,
    ∀ (a b c : ℕ), 0 < a → 0 < b → 0 < c → ({a, b, c} : Set ℕ).Pairwise Nat.Coprime → a + b = c →
    c < K * (radical <| a * b * c : ℝ)^(1 + ε) := by
  sorry

end ABC

theorem ABC.abc.variants.lt_constant_mul.disproof : ¬ (type_of% @ABC.abc.variants.lt_constant_mul) := sorry
