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
# Mersenne numbers of prime index

The Mersenne number with index $n$ is $M_n = 2^n - 1$. It is not known whether every
Mersenne number with prime index is square-free.

*References:*
- [Wikipedia: Mersenne number](https://en.wikipedia.org/wiki/Mersenne_number)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
-/

namespace MersenneNumber

/--
Are all Mersenne numbers of prime index square-free?

That is, is $M_p = 2^p - 1$ square-free for every prime $p$? Here `mersenne p` is Mathlib's
$2^p - 1$. The restriction to prime indices is essential: $M_6 = 63 = 3^2 \cdot 7$ is not
square-free.
-/
@[category research open, AMS 11]
theorem mersenne_number : answer(sorry) ↔ ∀ p : ℕ, p.Prime → Squarefree (mersenne p) := by
  sorry

/--
The restriction to prime indices is essential: $M_6 = 63 = 3^2 \cdot 7$ is not square-free.
-/
@[category test, AMS 11]
theorem not_squarefree_mersenne_six : ¬ Squarefree (mersenne 6) := by
  decide +kernel

end MersenneNumber
