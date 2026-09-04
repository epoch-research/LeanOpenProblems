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
# Prime quadruplets

A prime quadruplet is a set of four primes of the form $\{p, p + 2, p + 6, p + 8\}$.
This is the only prime constellation of length 4. The first prime quadruplets are
$\{5, 7, 11, 13\}$, $\{11, 13, 17, 19\}$, $\{101, 103, 107, 109\}$, and $\{191, 193, 197, 199\}$.

*References:*
- [Prime quadruplet Wikipedia page](https://en.wikipedia.org/wiki/prime_quadruplet)
- [List of unsolved problems in mathematics Wikipedia page](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
-/

namespace PrimeQuadruplet

/--
Are there infinitely many prime quadruplets? That is, are there infinitely many primes $p$
such that $p + 2$, $p + 6$ and $p + 8$ are also prime?
-/
theorem prime_quadruplet :
    
      {p : ℕ | Prime p ∧ Prime (p + 2) ∧ Prime (p + 6) ∧ Prime (p + 8)}.Infinite := by
  sorry

end PrimeQuadruplet

theorem PrimeQuadruplet.prime_quadruplet.disproof : ¬ (type_of% @PrimeQuadruplet.prime_quadruplet) := sorry
