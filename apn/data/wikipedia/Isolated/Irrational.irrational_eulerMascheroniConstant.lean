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
# Open questions on irrationality of numbers

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Irrational_number#Open_questions)
-/

open Real

local notation "e" => exp 1

-- See also corresponding transcendence conjectures
-- in `FormalConjectures.Wikipedia.SchanuelsConjecture`

namespace Irrational

/--
Is the Euler-Mascheroni constant $\gamma$ irrational?
-/
theorem irrational_eulerMascheroniConstant :
    Irrational eulerMascheroniConstant := by
  sorry

end Irrational

theorem Irrational.irrational_eulerMascheroniConstant.disproof : ¬ (type_of% @Irrational.irrational_eulerMascheroniConstant) := sorry
