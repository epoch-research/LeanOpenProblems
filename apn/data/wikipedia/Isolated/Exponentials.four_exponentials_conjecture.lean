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
**Four exponentials conjecture**
Let $x_0, x_1$ and $y_0, y_1$ be $\mathbb Q$-linearly independent pairs of complex numbers,
then some $e^{x_i y_j}$ is transcendental.
-/
theorem four_exponentials_conjecture (x : Fin 2 → ℂ) (y : Fin 2 → ℂ)
    (h1 : LinearIndependent ℚ x) (h2 : LinearIndependent ℚ y) :
    ∃ i j : Fin 2, Transcendental ℚ (exp (x i * y j)) := by
  sorry

end Exponentials

theorem Exponentials.four_exponentials_conjecture.disproof : ¬ (type_of% @Exponentials.four_exponentials_conjecture) := sorry
