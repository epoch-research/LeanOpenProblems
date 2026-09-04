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
# Can every integer be written as a sum of four perfect cubes?

The sum of four cubes problem asks whether every integer is the sum of four cubes of
integers. The cubes may be cubes of negative integers, in contrast to Waring's problem,
where the cubes must be cubes of non-negative integers. It is conjectured that the answer
is affirmative, but this has been neither proven nor disproven.

*References:*
 - [Wikipedia, Sum of four cubes problem](https://en.wikipedia.org/wiki/Sum_of_four_cubes_problem)
 - [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
-/

namespace CanEveryIntegerBeWrittenAsASumOfFourPerfectCubes

/--
Can every integer be written as a sum of four perfect cubes?

That is, is it true that for every integer $n$ there are integers $a, b, c, d$
(possibly negative) with $n = a^3 + b^3 + c^3 + d^3$?
The conjectured answer is affirmative.
-/
@[category research open, AMS 11]
theorem can_every_integer_be_written_as_a_sum_of_four_perfect_cubes :
    answer(sorry) ↔ ∀ n : ℤ, ∃ a b c d : ℤ, n = a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 := by
  sorry

end CanEveryIntegerBeWrittenAsASumOfFourPerfectCubes
