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
# Exponentials conjectures and theorems

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Four_exponentials_conjecture)
-/

open Complex

namespace Exponentials

/--
The four exponential conjecture would imply that for any irrational number $t$,
at least one of the numbers $2^t$ and $3^t$ is transcendental.
-/
theorem two_pow_three_pow_transcendental (t : ℝ) (h : Irrational t) :
    Transcendental ℚ (2 ^ t : ℝ) ∨ Transcendental ℚ (3 ^ t : ℝ) := by
  sorry

end Exponentials
