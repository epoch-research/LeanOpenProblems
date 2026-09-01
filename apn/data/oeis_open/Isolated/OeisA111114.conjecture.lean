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
# Integer part of $\mathrm{prime}(n)/\pi(n)$

Here $\mathrm{prime}(n)$ is the $n$-th prime number, and $\pi(n)$ is the prime-counting function.

*References:*
- [A111114](https://oeis.org/A111114)
-/

namespace OeisA111114

open Nat

/--
`a n` is the integer part of $\mathrm{prime}(n)/\pi(n)$.
Here $\mathrm{prime}(n)$ is the $n$-th prime number, and $\pi(n)$ is the prime-counting function.
The sequence is defined for $n \ge 2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Nat.nth Nat.Prime (n - 1)) / (Nat.primeCounting n)

open Filter

/--
Conjecture: As $n \rightarrow \infty$, there are infinitely many n's such that
$a(n)$ is greater than $a(n+1)$.
-/
theorem conjecture : ∃ᶠ n in atTop, a n > a (n + 1) := by
  sorry

end OeisA111114

theorem OeisA111114.conjecture.disproof : ¬ (type_of% @OeisA111114.conjecture) := sorry
