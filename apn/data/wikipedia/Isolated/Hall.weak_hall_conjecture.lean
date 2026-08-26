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
# Hall's conjecture

There exists a positive number $C$ such that for any integer $x, y$ with $y^2 \ne x^3$,
$|y^2 - x^3| > C \sqrt{|x|}$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Hall%27s_conjecture)
- L. Danilov, *The Diophantine equation $x^3 - y^2 = k$ and Hall's conjecture*, Mathematical notes of the Academy of Sciences of the USSR 32 (1982): 617-618
-/

open Real

namespace Hall

def HallIneq (C : ℝ) (e : ℝ) : Prop :=
  ∀ x y : ℤ, y ^ 2 ≠ x ^ 3 → |y ^ 2 - x ^ 3| > C * (|x| : ℝ) ^ e

def HallConjectureExp (e : ℝ) : Prop := ∃ C : ℝ, C > 0 ∧ HallIneq C e

/--
Weak form of Hall's conjecture: relax the exponent from $1/2$ to $1/2 - \varepsilon$.
-/
theorem weak_hall_conjecture (ε : ℝ) (hε : ε > 0) : HallConjectureExp (2⁻¹ - ε) := by
  sorry

end Hall
