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
# Erdős Problem 445

*References:*
- [erdosproblems.com/445](https://www.erdosproblems.com/445)
- [He00] Heath-Brown, D. R., Arithmetic applications of {K}loosterman sums. Nieuw Arch. Wiskd. (5)
  (2000), 380--384.
- [MathOverflow](https://mathoverflow.net/questions/69509/small-residue-classes-with-small-reciprocal)
-/

open Filter

namespace Erdos445

/--
The property that there exist $a,b\in(n,n+p^c)$ such that $ab\equiv 1\pmod{p}$.
-/
def Erdos445Prop (c : ℝ) (p n : ℕ) : Prop :=
  ∃ a b : ℕ,
    n < a ∧ (a : ℝ) < (n : ℝ) + (p : ℝ) ^ c ∧
    n < b ∧ (b : ℝ) < (n : ℝ) + (p : ℝ) ^ c ∧
    a * b ≡ 1 [MOD p]

/--
Is it true that, for any $c>1/2$, if $p$ is a sufficiently large prime then, for any
$n\geq 0$, there exist $a,b\in(n,n+p^c)$ such that $ab\equiv 1\pmod{p}$?

This is discussed in this MathOverflow question [MathOverflow].
-/
theorem erdos_445 :
    ∀ c : ℝ, c > 1 / 2 →
      ∀ᶠ p : ℕ in atTop, p.Prime → ∀ n : ℕ, Erdos445Prop c p n := by
  sorry

end Erdos445
