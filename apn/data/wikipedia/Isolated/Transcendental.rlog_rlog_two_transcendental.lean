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
# Open questions on transcendence of numbers

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Transcendental_number)
-/

open Real

namespace Transcendental

/--
$\log(\log(2))$ is transcendental.
-/
theorem rlog_rlog_two_transcendental : Transcendental ℚ ((2 : ℝ).log.log) := by
  sorry

end Transcendental

theorem Transcendental.rlog_rlog_two_transcendental.disproof : ¬ (type_of% @Transcendental.rlog_rlog_two_transcendental) := sorry
